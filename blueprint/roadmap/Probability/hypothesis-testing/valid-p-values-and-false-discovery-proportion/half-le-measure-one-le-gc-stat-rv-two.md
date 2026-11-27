# Two independent 𝒩(0, λ) null scores give P(T₀ ≥ 1) ≥ 1/2

Let `P` be a probability measure and let the two scores `Z_0, Z_1` of the [common-inflation
model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md), each with law `𝒩(0, λ)` under `P` for one `λ > 0`, be measurable
and independent. Then the [corrected statistic](gc-stat-rv.md) of gene `0` satisfies

`P(T_0 ≥ 1) ≥ 1/2`.

By exchangeability of the two independent scores, `P(Z_1² ≤ Z_0²) ≥ 1/2`, and almost surely
`T_0 ≥ 1` exactly when `Z_1² ≤ Z_0²` ([two-gene criterion](one-le-gc-stat-two-iff.md)). Since
[`P(χ²₁ > 1) < 1/2`](chi-sq-one-tail-one-lt-half.md), the calibration condition
`P(T_0 ≥ s) ≤ P(χ²₁ > s)` fails at `s = 1`.
