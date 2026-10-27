---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardo_binomial_alternating
---

# Gen Leonardo binomial alternating

The alternating binomial identities
`∑_i C(n,i) (-1)^{n-i} L_{k,2i+r} = L_{k,n+r} + k` and
`∑_i C(n,i) (-1)^{n-i} M_{k,2i+r} = M_{k,n+r} + 2k`, stated for `n ≥ 1`
(both identities fail at `n = 0` as extracted, where the sums equal
`L_{k,r}` and `M_{k,r}`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly (2024), Theorem 3.3 (`fq-2024-kuhapatanakul05292024-thm-3.3`).
