---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardo_shift
---

# Gen Leonardo shift

The shift identity
`L_{k,m} L_{k,n} - L_{k,m+t} L_{k,n-t}
= (-1)^{n-t+1} (L_{k,m-n+t-1} + k)(L_{k,t-1} + k)
- k (L_{k,m} + L_{k,n} - L_{k,m+t} - L_{k,n-t})`.

Stated here for `1 ≤ t ≤ n` with `n + 1 ≤ m + t` so that all indices are
nonnegative; the paper allows `t = 0` with `L_{k,-1}` read by backward
extension.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly (2024), Theorem 2.5 (`fq-2024-kuhapatanakul05292024-thm-2.5`).
