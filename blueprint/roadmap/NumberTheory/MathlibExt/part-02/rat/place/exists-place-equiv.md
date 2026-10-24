---
article_id: af_79062ffc62ada8e82b879ef0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Rat.Place.exists_place_equiv
---

# Exists place equiv

Translation of `Rat.AbsoluteValue.equiv_real_or_padic` into the
uniform place index.

`Rat.AbsoluteValue.equiv_real_or_padic` takes `f.IsNontrivial` and
concludes `f ≈ real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ padic p`;
this is repackaged as `∃ v : Place, f ≈ v.absoluteValue`, matching the
conclusion notation of Ostrowski directly.

## Depends on

- [Place](place.md)
- [Absolute Value](absolute-value.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Rat.Place](../../../../../../sources/v2/MathlibExt.md)
