---
article_id: af_7e431999a5d92c0891eeb237
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ramanujan_partition_congruence_mod_eleven
---

# Ramanujan Partition Congruence Mod Eleven

Ramanujan's partition congruence modulo 11: the number of unordered partitions of
`11 * m + 6` is divisible by 11 for every `m : ℕ`.

Proof: We follow Hirschhorn's Section 2 residue-section argument, using Euler's
pentagonal number theorem and Jacobi's cube identity.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Coeff jacobi Cube Series eq zero](ramanujan-partition-congruence/coeff-jacobi-cube-series-eq-zero.md)
- [Coeff jacobi Cube Series triangle](ramanujan-partition-congruence/coeff-jacobi-cube-series-triangle.md)
- [Dvd partition Function of dvd coeff pentagonal Series pow](ramanujan-partition-congruence/dvd-partition-function-of-dvd-coeff-pent.md)
- [Jacobi Cube Series](ramanujan-partition-congruence/jacobi-cube-series.md)
- [Pentagonal Series pow three](ramanujan-partition-congruence/pentagonal-series-pow-three.md)
- [Two mul choose two succ](ramanujan-partition-congruence/two-mul-choose-two-succ.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven](../../../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Ramanujan%27s_congruences
