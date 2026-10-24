---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalizedStirlingSecond_eq_sum
---

# Generalized Stirling Second eq sum

Characterization of `generalizedStirlingSecond`: under `m ≤ n` it equals the
exact source sum with coefficient `choose n i`, ordinary number
`stirlingSecond (n-i) m`, and power `x^i`, including both endpoints `i = 0` and
`i = n - m`. Source: Cereceda, arXiv:2401.13696v4, lines 132-142.

## Depends on

- [Generalized Stirling Second](generalized-stirling-second.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GeneralizedStirlingNumbers](../../../../../../../sources/v2/MathlibExt.md)
