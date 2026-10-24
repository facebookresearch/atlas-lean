---
article_id: af_c1732cbeddf46fb9fed6ed72
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.QPochhammer.qPochhammerInfRaw_two_one
---

# Q Pochhammer Inf Raw two one

Regression for the raw product outside the unit disk: the `tprod` fallback.

At `(a, q) = (2, 1)` every factor equals `-1`, so the family is not
multipliable and the total product `qPochhammerInfRaw 2 1` is `1` by the
`tprod` convention (`tprod_eq_one_of_not_multipliable`), not a limit of
partial products. This is exactly the silent wrong-value behaviour that the
gated `qPochhammerInf` (which demands `‖q‖ < 1`) rules out.

## Depends on

- [Q Pochhammer Inf Raw](q-pochhammer-inf-raw.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.QPochhammer](../../../../../../../sources/v2/MathlibExt.md)
