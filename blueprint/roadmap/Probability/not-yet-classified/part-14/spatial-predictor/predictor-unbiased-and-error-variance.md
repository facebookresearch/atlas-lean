# Predictor unbiased and error variance

Common-mean unbiased linear predictor: observations `Y i` and
target `X` are square-integrable with a common mean, and weights
`w` sum to `1`. Then the predictor `∑ i, w i * Y i` is unbiased for
`X`, and the prediction-error variance is
`Var X - 2 * (w ⬝ᵥ c) + w ⬝ᵥ (K *ᵥ w)` in terms of the covariance
matrix `K` and vector `c`.
