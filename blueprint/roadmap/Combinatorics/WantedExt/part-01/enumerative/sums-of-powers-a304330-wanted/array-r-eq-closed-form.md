---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted.arrayR_eq_closedForm
---

# Corollary 6

**Corollary 6**: for `1 ≤ m ≤ k`,
`R(k, m) = 2^{2k+m-1}·m!·Σ (2k)!/(b_1!⋯b_k!)·∏_{r=1}^k
(1/(4^r (2r)!))^{b_r}`, summed over the `k`-tuples
`b : Fin k → ℕ` with `Σ (r+1)·b_r = k` and `Σ b_r = m`
(the entry bounds `b_r ≤ k` are automatic from the weighted
sum).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted](../../../../../../sources/v2/WantedExt.md)
- José L. Cereceda, "Sums of Powers of Integers and the Sequence A304330", Corollary 6.
