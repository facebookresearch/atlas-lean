---
article_id: af_76c8baee20c2c03a1e4eef9e
declaration: def
origin: cited
statement: formalized
lean: Rat.Place.absoluteValue
---

# Absolute Value

Normalised real-valued absolute value attached to a place.

Reuses `Rat.AbsoluteValue.real` at infinity and `Rat.AbsoluteValue.padic`
at a finite prime. `Rat.AbsoluteValue.padic` takes `[Fact p.Prime]`,
so the proof in `prime` is turned into a local `Fact` dictionary.

## Depends on

- [Place](place.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Rat.Place](../../../../../../sources/v2/MathlibExt.md)
