# A tail-calibrated λ̂-corrected statistic has integral below 1

Let `P` be a measure on a measurable space `Ω`, let the random scores `Z_0, …, Z_{m-1}` be
measurable, and let `j` be a gene whose [corrected statistic](gc-stat-rv.md) satisfies the
calibration condition `P(T_j ≥ s) ≤ P(χ²₁ > s)` for every real `s`, where `P(χ²₁ > s)` is the [`χ²₁`
tail](../../../Biology/statistical-genetics/association-tests/genomic-control/chi-sq-one-tail.md). Then

`∫ T_j dP < 1 = E[χ²₁]`,

the integral of the nonnegative function `T_j`; when `P` is a probability measure it is the mean
`E[T_j]`. The layer-cake integral `∫_(0, ∞) P(T_j ≥ s) ds` stops at `s = m`, because `T_j ≤ m`
([bound](gc-stat-le-card.md)), while the `χ²₁` tail is [positive](chi-sq-one-tail-pos.md) beyond `m`
and [integrates to `1`](lintegral-chi-sq-one-tail.md).
