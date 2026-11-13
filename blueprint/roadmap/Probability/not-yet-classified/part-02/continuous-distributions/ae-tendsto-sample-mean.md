# Strong law of large numbers

**Strong law of large numbers** for the sample mean: if `X 0` is integrable and the `X i` are
pairwise independent with the law of `X 0`, then `x̄ₙ → E[X 0]` almost surely. This is Mathlib's
`ProbabilityTheory.strong_law_ae_real`, with exactly its hypotheses, transported to the
canonical sample mean by `sampleMean_fin_eq_sum_range_div`: pairwise independence suffices, and
no normalization of `P` is assumed. A finite-sample expectation identity
(`integral_sampleMean`) is not almost-sure or asymptotic consistency; the two are separate
theorems.
