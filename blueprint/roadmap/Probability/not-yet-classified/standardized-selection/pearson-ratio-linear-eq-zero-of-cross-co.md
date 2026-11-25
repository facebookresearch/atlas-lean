# Zero cross-covariance gives zero correlation for every linear score

Let `μ` be a
probability measure on `Ω`, `X : Ω → ℝⁿ` a random vector with all coordinates in `L²(μ)` and
positive definite covariance matrix `(cov[X_i, X_j; μ])`, and `H : Ω → ℝ` in `L²(μ)` with
`Var[H; μ] > 0` and `cov[X_i, H; μ] = 0` for every `i`. Then for every nonzero `b ∈ ℝⁿ`,
`pearsonRatio μ (b ⬝ᵥ X) H = 0`.
