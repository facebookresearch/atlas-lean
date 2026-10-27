---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalizedStirlingFirst_eq_sum
---

# Generalized Stirling First eq sum

Characterization of `generalizedStirlingFirst`: under `m ≤ n` it equals the
exact source sum with coefficient `choose (i+m) m`, ordinary number
`stirlingFirst n (i+m)`, and power `x^i`, including both endpoints `i = 0` and
`i = n - m`. Source: Cereceda, arXiv:2401.13696v4, lines 132-142.

## Depends on

- [Generalized Stirling First](generalized-stirling-first.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GeneralizedStirlingNumbers](../../../../../../../sources/v2/MathlibExt.md)
