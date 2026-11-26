# Genetic gain in covariance form

**Genetic gain in covariance form** (Hazel 1943, equation (3)). Let `μ` be a probability measure
on `Ω` and `M` a Smith–Hazel model on `n` traits under `μ` whose additive values and residuals
`(A, E)` are jointly Gaussian under `μ`. For every nonzero coefficient vector `b` and every
threshold `z`, the genetic gain from selecting the standardized upper event of `M.index b` at `z` is
`M.gain b z = inverseMillsRatio (-z) * (cov[M.index b, M.aggregate; μ] / σ_b)`, where
`σ_b = populationSD μ (M.index b)` and `inverseMillsRatio (-z) = φ(z) / Φ(-z)` is the intensity of
selection.
