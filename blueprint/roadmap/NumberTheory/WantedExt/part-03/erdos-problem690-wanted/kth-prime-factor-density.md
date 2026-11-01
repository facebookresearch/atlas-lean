---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.ErdosProblem690Wanted.kthPrimeFactorDensity
---

# Kth Prime Factor Density

Natural (asymptotic) density of a set of naturals: the canonical
`Set.HasDensity` from `MathlibExt.Data.Set.Density` (default ambient set);
for naturals it is the limit of `|S ∩ [0, N)| / N`.
`dₖ(p)`: the density of integers whose `k`-th smallest prime factor
is `p`, chosen by Hilbert choice (the unique limit when it exists).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Kth Smallest Prime Factor](is-kth-smallest-prime-factor.md)
- [Has Density](../../../../Data/MathlibExt/set/density/has-density.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.ErdosProblem690Wanted](../../../../../sources/v2/WantedExt.md)
