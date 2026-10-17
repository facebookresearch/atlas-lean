---
article_id: af_75105947106a6fe9d3a7989c
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.dusart_log_prime_sum
---

# Dusart log prime sum

Dusart explicit Mertens first theorem: for `x ≥ 912560`,
`∑_{p ≤ x} log p / p = log x + M + E` with `|E| ≤ 0.3 / (log x)^2`,
where `M` is the Theorem 5.7 constant. The sum ranges over
`Finset.range (⌊x⌋₊ + 1)` filtered by `Nat.Prime`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.DusartMertensLogSumWanted](../../../../../../../sources/v2/WantedExt.md)
- Pierre Dusart, *Explicit estimates of some functions over primes*, Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.7.
