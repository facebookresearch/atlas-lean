# Gaussian central second moment

`∫ (x - μ) ^ 2 ∂N(μ, v) = v`. Proved from Mathlib's
variance of the Gaussian, `ProbabilityTheory.variance_id_gaussianReal`, unfolded by
`ProbabilityTheory.variance_eq_integral`; no moment-generating-function or
characteristic-function differentiation is used. It holds for every `v : ℝ≥0`, including the
degenerate `v = 0`, where `gaussianReal μ 0` is the Dirac mass at `μ`.
