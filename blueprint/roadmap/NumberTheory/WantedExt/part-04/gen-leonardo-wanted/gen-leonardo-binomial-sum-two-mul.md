---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardo_binomial_sum_two_mul
---

# Gen Leonardo binomial sum two mul

The even-order binomial identities
`∑_i C(2m,i) L_{k,2i+r} = 5^m L_{k,2m+r} + k (5^m - 2^{2m})` and
`∑_i C(2m,i) M_{k,2i+r} = 5^m M_{k,2m+r} + 2k (5^m - 2^{2m})`.

This is the even case of the paper's Theorem 3.2; the odd case as
printed is false (at `k = n = 1, r = 0` the first odd identity reads
`4 = 6`) and is not formalized.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly (2024), Theorem 3.2, even case (`fq-2024-kuhapatanakul05292024-thm-3.2`).
