# Sequence form

For an i.i.d. square-integrable sequence `X 0, X 1, …` and `n ≥ 2`, the
unbiased sample variance `FiniteProbability.sampleVarUnbiased` of the first `n` observations
(the restriction `fun i : Fin n => X i ω`) is integrable and unbiased for `Var (X 0)`.
Derived from `integral_sampleVariance_of_iid_fin` by restriction to `Fin n`.
