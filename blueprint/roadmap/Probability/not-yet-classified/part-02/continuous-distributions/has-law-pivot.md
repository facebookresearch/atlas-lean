# The pivot has Student's `t` law

Under `StudentTPivotLaw` the pivot
`√n (x̄ₙ - μ) / sₙ` has law `studentTMeasure (n - 1)`. The tuple
`(X 0, …, X (n - 1))` has law `Measure.pi (fun _ => gaussianReal μ (σ ^ 2).toNNReal)` by
`iIndepFun.hasLaw_pi`; composing with the one-sample `t` statistic of
`ProbabilityTheory.map_tStatistic_pi_gaussianReal` gives the pivot law, since the pivot is
that statistic of the tuple, by `FiniteProbability.sampleMean_eq_sum_div` and
`FiniteProbability.sampleVarUnbiased_eq_sum_div`.
