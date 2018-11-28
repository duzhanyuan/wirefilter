use ast::Filter;
use failure::Fail;
use fnv::FnvBuildHasher;
use indexmap::map::{Entry, IndexMap};
use lex::{complete, expect, span, take_while, LexErrorKind, LexResult, LexWith};
use serde::{Deserialize, Serialize, Serializer};
use std::{
    cmp::{max, min},
    error::Error,
    fmt::{self, Debug, Display, Formatter},
    iter::FromIterator,
    ptr,
};
use types::{GetType, Type};

#[derive(PartialEq, Eq, Clone, Copy)]
pub(crate) struct Field<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl<'s> Serialize for Field<'s> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.name().serialize(ser)
    }
}

impl<'s> Debug for Field<'s> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for Field<'s> {
    fn lex_with(mut input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        loop {
            input = take_while(input, "identifier character", |c| {
                c.is_ascii_alphanumeric() || c == '_'
            })?.1;

            match expect(input, ".") {
                Ok(rest) => input = rest,
                Err(_) => break,
            };
        }

        let name = span(initial_input, input);

        let field = scheme
            .get_field_index(name)
            .map_err(|err| (LexErrorKind::UnknownField(err), name))?;

        Ok((field, input))
    }
}

impl<'s> Field<'s> {
    pub fn name(&self) -> &'s str {
        self.scheme.fields.get_index(self.index).unwrap().0
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn scheme(&self) -> &'s Scheme {
        self.scheme
    }
}

impl<'s> GetType for Field<'s> {
    fn get_type(&self) -> Type {
        *self.scheme.fields.get_index(self.index).unwrap().1
    }
}

#[derive(Debug, PartialEq, Fail)]
#[fail(display = "unknown field")]
pub struct UnknownFieldError;

#[derive(Debug, PartialEq)]
pub struct ParseError<'i> {
    kind: LexErrorKind,
    input: &'i str,
    line_number: usize,
    span_start: usize,
    span_len: usize,
}

impl<'i> Error for ParseError<'i> {}

impl<'i> ParseError<'i> {
    pub(crate) fn new(mut input: &'i str, (kind, span): (LexErrorKind, &'i str)) -> Self {
        let mut span_start = span.as_ptr() as usize - input.as_ptr() as usize;

        let (line_number, line_start) = input[..span_start]
            .match_indices('\n')
            .map(|(pos, _)| pos + 1)
            .scan(0, |line_number, line_start| {
                *line_number += 1;
                Some((*line_number, line_start))
            }).last()
            .unwrap_or_default();

        input = &input[line_start..];

        span_start -= line_start;
        let mut span_len = span.len();

        if let Some(line_end) = input.find('\n') {
            input = &input[..line_end];
            span_len = min(span_len, line_end - span_start);
        }

        ParseError {
            kind,
            input,
            line_number,
            span_start,
            span_len,
        }
    }
}

impl<'i> Display for ParseError<'i> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Filter parsing error ({}:{}):",
            self.line_number + 1,
            self.span_start + 1
        )?;

        writeln!(f, "{}", self.input)?;

        for _ in 0..self.span_start {
            write!(f, " ")?;
        }

        for _ in 0..max(1, self.span_len) {
            write!(f, "^")?;
        }

        writeln!(f, " {}", self.kind)?;

        Ok(())
    }
}

#[derive(Default, Deserialize)]
#[serde(transparent)]
pub struct Scheme {
    fields: IndexMap<String, Type, FnvBuildHasher>,
}

impl FromIterator<(String, Type)> for Scheme {
    fn from_iter<I: IntoIterator<Item = (String, Type)>>(iter: I) -> Self {
        Scheme {
            fields: IndexMap::from_iter(iter),
        }
    }
}

impl PartialEq for Scheme {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other)
    }
}

impl Eq for Scheme {}

impl<'s> Scheme {
    pub fn add_field(&mut self, name: String, ty: Type) {
        match self.fields.entry(name) {
            Entry::Occupied(entry) => {
                panic!("Tried to register field {} with type {:?} but it's already registered with type {:?}", entry.key(), ty, entry.get())
            }
            Entry::Vacant(entry) => {
                entry.insert(ty);
            }
        }
    }

    pub(crate) fn get_field_index(&'s self, name: &str) -> Result<Field<'s>, UnknownFieldError> {
        match self.fields.get_full(name) {
            Some((index, ..)) => Ok(Field {
                scheme: self,
                index,
            }),
            None => Err(UnknownFieldError),
        }
    }

    pub(crate) fn get_field_count(&self) -> usize {
        self.fields.len()
    }

    pub fn parse<'i>(&'s self, input: &'i str) -> Result<Filter<'s>, ParseError<'i>> {
        complete(Filter::lex_with(input.trim(), self)).map_err(|err| ParseError::new(input, err))
    }
}

#[test]
fn test_parse_error() {
    use indoc::{indoc, indoc_impl};

    let scheme: &Scheme = &[("num", Type::Int)]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    {
        let err = scheme.parse("xyz").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownField(UnknownFieldError),
                input: "xyz",
                line_number: 0,
                span_start: 0,
                span_len: 3
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:1):
                xyz
                ^^^ unknown field
                "#
            )
        );
    }

    {
        let err = scheme.parse("xyz\n").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownField(UnknownFieldError),
                input: "xyz",
                line_number: 0,
                span_start: 0,
                span_len: 3
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:1):
                xyz
                ^^^ unknown field
                "#
            )
        );
    }

    {
        let err = scheme.parse("\n\n    xyz").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownField(UnknownFieldError),
                input: "    xyz",
                line_number: 2,
                span_start: 4,
                span_len: 3
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (3:5):
                    xyz
                    ^^^ unknown field
                "#
            )
        );
    }

    {
        let err = scheme
            .parse(indoc!(
                r#"
                num == 10 or
                num == true or
                num == 20
                "#
            )).unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ExpectedName("digit"),
                input: "num == true or",
                line_number: 1,
                span_start: 7,
                span_len: 7
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (2:8):
                num == true or
                       ^^^^^^^ expected digit
                "#
            )
        );
    }
}

#[test]
fn test_field() {
    let scheme = &[
        ("x", Type::Bytes),
        ("x.y.z0", Type::Int),
        ("is_TCP", Type::Bool),
    ]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    assert_ok!(
        Field::lex_with("x;", scheme),
        scheme.get_field_index("x").unwrap(),
        ";"
    );

    assert_ok!(
        Field::lex_with("x.y.z0-", scheme),
        scheme.get_field_index("x.y.z0").unwrap(),
        "-"
    );

    assert_ok!(
        Field::lex_with("is_TCP", scheme),
        scheme.get_field_index("is_TCP").unwrap(),
        ""
    );

    assert_err!(
        Field::lex_with("x..y", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        ".y"
    );

    assert_err!(
        Field::lex_with("x.#", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        "#"
    );

    assert_err!(
        Field::lex_with("x.y.z;", scheme),
        LexErrorKind::UnknownField(UnknownFieldError),
        "x.y.z"
    );
}
