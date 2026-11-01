---
article_id: af_a96fe7e5d26a5c249b68468c
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.dusart_reciprocal_prime_sum
---

# Dusart reciprocal prime sum

Dusart explicit Mertens second theorem: for `x ≥ 2278383`,
`∑_{p ≤ x} 1 / p = log log x + B + E` with `|E| ≤ 0.2 / (log x)^3`,
where `B` is the Meissel–Mertens constant. The sum ranges over
`Finset.range (⌊x⌋₊ + 1)` filtered by `Nat.Prime`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumWanted](../../../../../../../sources/v2/WantedExt.md)
- Pierre Dusart, *Explicit estimates of some functions over primes*, Ramanujan J. 45(1) (2018), 227–251, <https://doi.org/10.1007/s11139-016-9839-4>, Theorem 5.6.
