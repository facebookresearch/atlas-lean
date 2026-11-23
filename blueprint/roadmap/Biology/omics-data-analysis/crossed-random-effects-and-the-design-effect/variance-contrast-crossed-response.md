# Variance of a linear combination of the Gaussian crossed response

Let `I`, `J` and `p` be finite index types, `P` a probability measure on a space `Ω`, and
`σ_s², σ_w², σ_e² ≥ 0`. Let the random effects `γ : Ω → ℝ^(I ⊔ J)` and the residuals
`ε : Ω → ℝ^(I × J)` be measurable and independent, with `γ ~ N(0, G)` for the
[crossed random-effects covariance](crossed-cov.md) `G` and `ε ~ N(0, σ_e² I)`. For a fixed-effects
design `X` with rows `I × J` and columns `p` and coefficients `β ∈ ℝ^p`, let `Y = X β + Z γ + ε`,
with `Z` the [crossed design](crossed-design.md). Then for every coefficient vector `c : I × J → ℝ`,

`Var(∑_k c_k Y_k) = ∑_k ∑_l c_k c_l ([k_1 = l_1] σ_s² + [k_2 = l_2] σ_w² + [k = l] σ_e²)`,

the sums running over all observations `k = (k_1, k_2)` and `l = (l_1, l_2)` in `I × J`, where `[·]`
is `1` if the condition holds and `0` otherwise. No condition such as `∑_k c_k = 0` is imposed, so
the formula holds for every linear combination of the observations, a planned contrast in
particular.
