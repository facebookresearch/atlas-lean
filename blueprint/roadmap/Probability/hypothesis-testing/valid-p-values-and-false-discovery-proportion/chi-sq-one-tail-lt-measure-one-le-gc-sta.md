# Two independent null genes: the λ̂ test is anti-conservative at 1

Let `P` be a probability measure and let the two scores `Z_0, Z_1` of the [common-inflation
model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md), each with law `𝒩(0, λ)` under `P` for one `λ > 0`, be measurable
and independent. The estimated-factor test of gene `0` at threshold `1` rejects more often than the
nominal level:

`P(χ²₁ > 1) < P(T_0 ≥ 1)`,

where `T_0` is the [corrected statistic](gc-stat-rv.md) and `P(χ²₁ > 1)` the [`χ²₁`
tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). Indeed [`P(T_0 ≥ 1) ≥ 1/2`](half-le-measure-one-le-gc-stat-rv-two.md)
while [`P(χ²₁ > 1) < 1/2`](chi-sq-one-tail-one-lt-half.md) (its value is `≈ 0.317`), although
[dividing by the true `λ` is exactly calibrated](../../../Biology/statistical-genetics/association-tests/genomic-control/measure-reject-eq.md).
