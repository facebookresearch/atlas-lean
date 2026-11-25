# Zero cross-covariance gives zero response for every linear score

Let `μ` be a
probability measure on `Ω`, `X : Ω → ℝⁿ` a measurable random vector and `H : Ω → ℝ` with `(X, H)`
jointly Gaussian under `μ`, the covariance matrix `(cov[X_i, X_j; μ])` positive definite, and
`cov[X_i, H; μ] = 0` for every `i`. Then for every nonzero `b ∈ ℝⁿ` and every threshold `z ∈ ℝ`,
selecting the standardized upper event of the score `b ⬝ᵥ X` at `z` does not change the mean of
`H`: the conditional mean shift is `0`.
