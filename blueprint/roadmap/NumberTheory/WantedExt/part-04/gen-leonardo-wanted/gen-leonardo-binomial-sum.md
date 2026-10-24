---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardo_binomial_sum
---

# Gen Leonardo binomial sum

The binomial-convolution identities
`∑_i C(n,i) L_{k,i+r} = L_{k,2n+r} - k (2^n - 1)` and
`∑_i C(n,i) M_{k,i+r} = M_{k,2n+r} - 2k (2^n - 1)`.

Parts (iii) and (iv) of the paper's Theorem 3.1 (alternating sums)
are not formalized: as printed they involve the backward index
`L_{k,n-r-2}` and fail, for example at `k = 1, n = 3, r = 1` under
the backward extension (left side `2`, printed right side `-2`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly (2024), Theorem 3.1 (i),(ii) (`fq-2024-kuhapatanakul05292024-thm-3.1`).
