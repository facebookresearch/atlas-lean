---
article_id: af_d88c7a6e2fe5258e30f53d2f
declaration: theorem
origin: cited
---

# Christol theorem

Christol's theorem: algebraicity iff `p`-automaticity of coefficients.

Polynomial-relation interpretation: `IsAlgebraic (Polynomial K) f` asserts a
denominator-cleared nonzero polynomial relation over `K[X]` satisfied by `f`,
which is the formalization of algebraicity over the rational function field
`K(t)`; it is not integrality (`IsIntegral`). The right side is
`p`-automaticity (base `p`, not base `q`) of `fun n => PowerSeries.coeff n f`.
The positivity `0 < r` is preserved verbatim from the source.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Algebra.PowerSeries.ChristolTheorem](../../../../../sources/v2/WantedExt.md)
- Adamczewski--Bell, arXiv:1205.4091v1, lines 260--265: for `q` a positive integral power of the characteristic prime `p`, a series over `F_q` is algebraic over `F_q(t)` iff its coefficient sequence is `p`-automatic.
