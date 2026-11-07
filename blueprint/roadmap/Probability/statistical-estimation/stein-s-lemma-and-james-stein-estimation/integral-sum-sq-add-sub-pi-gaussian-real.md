# Stein's unbiased risk estimate

For `X ~ N(θ, I_p)` and an estimator `X + g(X)` whose
coordinates `gᵢ` are square integrable and satisfy the hypotheses of Stein's lemma in the `i`-th
coordinate with partial derivative `dgᵢ`, the quadratic risk is
`p + E[∑ gᵢ(X)² + 2 ∑ dgᵢ(X)]`.
