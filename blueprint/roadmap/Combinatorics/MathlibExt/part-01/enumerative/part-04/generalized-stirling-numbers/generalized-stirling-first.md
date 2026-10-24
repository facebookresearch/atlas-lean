---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.generalizedStirlingFirst
---

# Generalized Stirling First

Generalized Stirling numbers of the first kind, after Carlitz and Broder,
as recorded in Cereceda (arXiv:2401.13696v4, lines 132-142; Axioms 14 (2025), 746):
`[n,m]_x = ∑_{i=0}^{n-m} choose (i+m) m * stirlingFirst n (i+m) * x^i`
for `m ≤ n`, with `x` real. The definition below uses the displayed finite sum
for every `n, m`; when `m > n`, `n - m + 1 = 1` and the single ordinary term
vanishes, giving `0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GeneralizedStirlingNumbers](../../../../../../../sources/v2/MathlibExt.md)
