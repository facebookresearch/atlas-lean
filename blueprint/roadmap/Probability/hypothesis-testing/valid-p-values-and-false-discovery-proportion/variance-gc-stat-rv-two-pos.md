# Two independent null genes: T₀ has positive variance

Let `P` be a probability measure and let the two scores `Z_0, Z_1` of the [common-inflation
model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md), each with law `𝒩(0, λ)` under `P` for one `λ > 0`, be measurable
and independent. Then the [corrected statistic](gc-stat-rv.md) `T_0` is nondegenerate:
`Var(T_0) > 0`. Indeed `T_0` is bounded, and
[`P(T_0 ≥ 1) ≥ 1/2`](half-le-measure-one-le-gc-stat-rv-two.md) and
[`P(T_0 < 1) ≥ 1/2`](half-le-measure-gc-stat-rv-two-lt-one.md), so `T_0` is not almost surely
constant.
