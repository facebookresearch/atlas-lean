# Global null: tail calibration fails when scores are a.s. not all zero

Let `P` be a probability measure on a measurable space `Ω`, `m ≥ 1`, and let the random scores
`Z_0, …, Z_{m-1}` be measurable and almost surely not all zero. Then the [corrected
statistics](gc-stat-rv.md), with the [real-valued `χ²₁` tail](chi-sq-one-tail-real.md) as reference
tail, are not a [tail-calibrated
family](../benjamini-hochberg-procedure/is-tail-calibrated-family.md) when every
gene is a true null: the condition `P(T_j ≥ s) ≤ P(χ²₁ > s)` for every gene `j` and every real `s`
is impossible. It would give `E[T_j] < 1` for every `j` ([integral
bound](lintegral-gc-stat-rv-lt-one.md)), hence `∑ⱼ E[T_j] < m`, while `∑ⱼ E[T_j] = m` ([sum of
means](sum-lintegral-gc-stat-rv.md)) because `∑ⱼ T_j = m` almost surely. No Gaussianity,
independence or other assumption on the law of the scores is used. So, for such scores, the
condition can hold only for a set of true nulls that leaves out some gene.
