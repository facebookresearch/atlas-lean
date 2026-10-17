---
article_id: af_248da4c50332ba8749f39567
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.QPochhammer.qPochhammerInfRaw
---

# Q Pochhammer Inf Raw

Raw complex infinite q-Pochhammer product `(a;q)_∞`, total in `q`.

This is Mathlib's `tprod` over `ℕ` of the zero-based factor family
`1 - a * q ^ n`. When the factors are not multipliable (in particular for most
`q` with `‖q‖ ≥ 1`), `tprod` takes its conventional default value `1`; see
`qPochhammerInfRaw_two_one`. Use the canonical `qPochhammerInf`, which requires
convergence evidence `‖q‖ < 1`, unless this fallback behaviour is intended.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.QPochhammer](../../../../../../../sources/v2/MathlibExt.md)
