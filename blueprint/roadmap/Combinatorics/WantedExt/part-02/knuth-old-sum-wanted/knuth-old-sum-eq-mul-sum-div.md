---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.KnuthOldSumWanted.knuthOldSum_eq_mul_sum_div
---

# Theorem 1

**Theorem 1**: for nonnegative integers `n` and `j`, with
`N = n + 2j + 1`,
`Σ_{k=0}^n C(N, n-k)·(2^{n-k}+1)·2^{n-k-1}·(-1)^k
= C(N, n)·Σ_{k=0}^n [C(n, k)/C(2j+1+k, 2j+1)]·(2^{n-k}+1)·2^{n-k-1}·(-1)^k`
(Equation (1), with the weight in the form `(4^m + 2^m)/2`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.KnuthOldSumWanted](../../../../../sources/v2/WantedExt.md)
- Akalu Tefera and Aklilu Zeleke, "Combinatorial Identities Inspired by Knuth's Old Sum", Theorem 1.
