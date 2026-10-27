---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.KnuthOldSumWanted.knuthOldSum_eq_sum_pow
---

# Theorem 2

**Theorem 2**: for nonnegative integers `n` and `j`, with
`N = n + 2j + 1`,
`Σ_{k=0}^n C(N, n-k)·(2^{n-k}+1)·2^{n-k-1}·(-1)^k
= Σ_{k=0}^n C(2j+k, k)·2^{k-1}·(1 + 2^k·3^{n-k})`
(Equation (2), with both weights in division-by-`2` form).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.KnuthOldSumWanted](../../../../../sources/v2/WantedExt.md)
- Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities Inspired by Knuth's Old Sum", Theorem 2.
