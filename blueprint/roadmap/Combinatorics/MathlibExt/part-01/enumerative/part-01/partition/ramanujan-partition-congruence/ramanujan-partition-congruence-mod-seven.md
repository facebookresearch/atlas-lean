---
article_id: af_123b79d290526cca3d3a4aed
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ramanujan_partition_congruence_mod_seven
---

# Ramanujan partition congruence mod seven

Ramanujan's partition congruence modulo 7: the number of unordered partitions of
`7 * m + 5` is divisible by 7 for every `m : ℕ`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Coeff jacobi Cube Series eq zero](coeff-jacobi-cube-series-eq-zero.md)
- [Coeff jacobi Cube Series triangle](coeff-jacobi-cube-series-triangle.md)
- [Dvd partition Function of dvd coeff pentagonal Series pow](dvd-partition-function-of-dvd-coeff-pent.md)
- [Jacobi Cube Series](jacobi-cube-series.md)
- [Pentagonal Series pow three](pentagonal-series-pow-three.md)
- [Two mul choose two succ](two-mul-choose-two-succ.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence](../../../../../../../../sources/v2/MathlibExt.md)
- S. Ramanujan, "Some properties of p(n), the number of partitions of n", Proceedings of the Cambridge Philosophical Society 19 (1919), 207–210, where the congruence is stated and proved. The proof follows Ramanujan's argument there: the sixth power of Euler's product is the square of Jacobi's cube series, and a sum of two squares divisible by 7 has both terms divisible by 7.
