---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardo_sq_sum_diff
---

# Gen Leonardo sq sum diff

The sum-and-difference square identities:
`L_{k,m+n}^2 - L_{k,m-n}^2
= (L_{k,2m+1} + k)(L_{k,2n-1} + k) - 2k (L_{k,m+n} - L_{k,m-n})` and
`L_{k,m+n}^2 + L_{k,m-n-1}^2
= (L_{k,2m} + k)(L_{k,2n} + k) - 2k (L_{k,m+n} + L_{k,m-n-1}) - 2k^2`.

In part (ii) the last summand inside the parenthesis is read as
`L_{k,m-n-1}`. The paper as printed shows `L_{k,m-n}` there, which is
false: at `k = 1, m = 3, n = 1` the printed identity reads `82 = 78`.
The reading used here agrees with the paper's outline derivation and
was verified computationally for `k ∈ {0,1,2,3}`, `m ≤ 11`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly (2024), Theorem 2.6 (`fq-2024-kuhapatanakul05292024-thm-2.6`).
