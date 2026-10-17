---
article_id: af_f8319331c755b9ef8de3bee0
declaration: def
origin: cited
statement: formalized
lean: Rat.Place.embedding
---

# Embedding

Canonical ring embedding `ℚ →+* ℚ_v`.

At infinity this is `Rat.castHom ℝ`; at a finite prime it is
`Rat.castHom (Padic p)` under the local `Fact p.Prime` instance.

## Depends on

- [Place](place.md)
- [Completed Field](completed-field.md)
- [Completed Field Bundle](completed-field-bundle.md)
- [Bundle](bundle.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Rat.Place](../../../../../../sources/v2/MathlibExt.md)
