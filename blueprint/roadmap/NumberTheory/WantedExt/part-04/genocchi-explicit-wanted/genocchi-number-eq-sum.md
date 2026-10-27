---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.GenocchiExplicitWanted.genocchiNumber_eq_sum
---

# Theorem 1

**Theorem 1**: for positive `n, r` with `n ≥ r + 1`,
`Gₙ = (-1)ⁿ n ∑_{k=1}^{n-r} (∑_{j=0}^r (-1)^{k+j+r}
(k+j-1)!/2^{k+j-1} S(r,j)) S(n-r,k)` (the paper's first
equality `2(1-2ⁿ)Bₙ = Gₙ` is MathlibExt's proved
`genocchiNumber_eq_bernoulli`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenocchiExplicitWanted](../../../../../sources/v2/WantedExt.md)
- Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas for Bernoulli and Genocchi Numbers", Theorem 1.
