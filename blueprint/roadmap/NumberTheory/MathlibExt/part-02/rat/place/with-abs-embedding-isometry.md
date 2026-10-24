---
article_id: af_2d7e624e6bb32ed092fb3e78
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Rat.Place.withAbsEmbedding_isometry
---

# With Abs Embedding isometry

The `WithAbs` embedding is an isometry.

Uses `WithAbs.norm_eq_apply_ofAbs` to rewrite the `WithAbs` norm to the
absolute value, `embedding_norm_eq_absoluteValue` for the target norm,
and `AddMonoidHomClass.isometry_of_norm`.

## Depends on

- [Place](place.md)
- [Completed Field](completed-field.md)
- [Completed Field Bundle](completed-field-bundle.md)
- [Absolute Value](absolute-value.md)
- [Bundle](bundle.md)
- [With Abs Embedding](with-abs-embedding.md)

## Proof depends on

- [Embedding](embedding.md)
- [Embedding norm eq absolute Value](embedding-norm-eq-absolute-value.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Rat.Place](../../../../../../sources/v2/MathlibExt.md)
