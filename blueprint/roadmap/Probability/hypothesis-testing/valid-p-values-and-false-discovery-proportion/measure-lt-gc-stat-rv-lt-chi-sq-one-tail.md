# Strictly conservative against χ²₁ at every threshold c ≥ m

Let `P` be any measure on a measurable space `Ω`, `Z_0, …, Z_{m-1}` any real functions on `Ω`
(random scores) and `j` a gene. At every threshold `c ≥ m`, the [corrected statistic](gc-stat-rv.md)
`T_j` is strictly conservative against `χ²₁`:

`P(T_j > c) < P(χ²₁ > c)`,

where `P(χ²₁ > c)` is the [`χ²₁` tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). The left side is `0` ([no
rejection](measure-lt-gc-stat-rv-eq-zero.md)) and the right side is positive, since `c ≥ m ≥ 0`
([positivity](chi-sq-one-tail-pos.md)).
