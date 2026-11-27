# Zero cross-covariance gives zero Pearson quotient for every linear score

Let `μ` be a
probability measure on `Ω`, `X : Ω → ℝⁿ` with all coordinates in `L²(μ)` and positive definite
covariance matrix `(cov[X_i, X_j; μ])`, and `H : Ω → ℝ` in `L²(μ)` with `Var[H; μ] > 0` and
`cov[X_i, H; μ] = 0` for every `i`. Then for every nonzero `b ∈ ℝⁿ`, the quotient
`pearsonRatio μ (b ⬝ᵥ X) H` equals `0` (and equals the Pearson correlation of `b ⬝ᵥ X` and `H`
since both scores lie in `L²(μ)` with positive variances; the proof itself uses only
`cov[b ⬝ᵥ X, H; μ] = 0`).
