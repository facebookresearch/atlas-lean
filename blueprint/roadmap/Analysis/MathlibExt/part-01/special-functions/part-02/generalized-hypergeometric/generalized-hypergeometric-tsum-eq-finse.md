---
article_id: af_c021ae43c18bf3c16a06355a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometric_tsum_eq_finset_sum
---

# Generalized Hypergeometric tsum eq finset sum

Core algebraic identification of the `tsum` with the finite sum over
`Finset.range (N+1)` when an upper parameter is `-(N : ℂ)`. No admissibility
hypothesis is needed: the equality holds because the upper Pochhammer factor
vanishes for `n > N`; the lower product never enters.

## Depends on

- [Generalized Hypergeometric Coefficient](generalized-hypergeometric-coefficient.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.GeneralizedHypergeometric](../../../../../../../sources/v2/MathlibExt.md)
