# Two independent null genes: the λ̂ family is not tail-calibrated

Let `P` be a probability measure and let the two scores `Z_0, Z_1` of the [common-inflation
model](../../../Biology/statistical-genetics/association-tests/genomic-control/common-inflation-model.md), each with law `𝒩(0, λ)` under `P` for one `λ > 0`, be measurable
and independent. Then the [corrected statistics](gc-stat-rv.md) `T_0, T_1`, with the [real-valued
`χ²₁` tail](chi-sq-one-tail-real.md) as reference tail, are not a [tail-calibrated
family](../benjamini-hochberg-procedure/is-tail-calibrated-family.md) for any
set `H0` of true nulls containing gene `0`: the condition `P(T_0 ≥ s) ≤ P(χ²₁ > s)` [fails at
`s = 1`](chi-sq-one-tail-lt-measure-one-le-gc-sta.md). So calibration of the estimated-factor
statistics does not follow from the calibration of dividing by the true `λ`, which [holds in this
model](../../../Biology/statistical-genetics/association-tests/genomic-control/measure-reject-eq.md).
