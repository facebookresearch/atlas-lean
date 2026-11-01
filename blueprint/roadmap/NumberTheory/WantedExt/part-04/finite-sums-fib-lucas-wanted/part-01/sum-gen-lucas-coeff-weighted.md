---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.FiniteSumsFibLucasWanted.sum_genLucasCoeff_weighted
---

# Corollary 13

**Corollary 13** (corrected):
`∑_{n=0}^m (2/√5)ⁿ C(m,n) cₙ = 2√5^{1-m}` with
`cₙ = genLucasCoeff n`; expanding `cₙ` gives the printed
double sum `∑ 2ⁿ√5^{k-n} C(n,k) C(m,n) Gₖ L_{n-k+1}/(n-k+1)`
plus the correction `∑ (2/√5)ⁿ C(m,n) 2√5^{n+1}
G_{n+1}/(n+1)`. The printed form holds only for odd `m`
(at `m = 2` it gives `12√5/5` against `2√5/5`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FiniteSumsFibLucasWanted](../../../../../../sources/v2/WantedExt.md)
- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Corollary 13.
