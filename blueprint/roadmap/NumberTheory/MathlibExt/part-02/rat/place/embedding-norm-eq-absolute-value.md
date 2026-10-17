---
article_id: af_99e9dfa1bcc1ddb456023405
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Rat.Place.embedding_norm_eq_absoluteValue
---

# Embedding norm eq absolute Value

The embedding norm is the selected absolute value:

`‖embedding v q‖ = v.absoluteValue q`.

At infinity this follows by unfolding the selected embedding and absolute
value with `Rat.AbsoluteValue.real_eq_abs` and closing the resulting
`|(q : ℝ)| = ↑|q|` with `Rat.cast_abs` in the reverse direction;
`p`-adically it is `Padic.eq_padicNorm`.

## Depends on

- [Place](place.md)
- [Completed Field](completed-field.md)
- [Completed Field Bundle](completed-field-bundle.md)
- [Absolute Value](absolute-value.md)
- [Bundle](bundle.md)
- [Embedding](embedding.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Rat.Place](../../../../../../sources/v2/MathlibExt.md)
