# Nb Shape Fisher Info

The expected (Fisher) shape information of one count with linear predictor `η`,
`E[∑_{j<y} 1 / (θ + j)²] - 1 / θ + 1 / (θ + μ)` for `y ~ NB(θ, μ)` and `μ = e^η`: the mean of
`nbShapeObsInfo θ y η` (`hasSum_nbShapeObsInfo_mul_negBinomialReal`). The series is the
trigamma difference `ψ₁(θ) - E ψ₁(θ + y)`; no closed form is used.
