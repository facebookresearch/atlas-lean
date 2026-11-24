# Covariances of the Gaussian crossed random-intercept response

Let `I`, `J` and `p` be finite index types, `P` a probability measure on a space `Ω`, and
`σ_s², σ_w², σ_e² ≥ 0`. Let the random effects `γ : Ω → ℝ^(I ⊔ J)` and the residuals
`ε : Ω → ℝ^(I × J)` be measurable and independent, with `γ ~ N(0, G)` for the
[crossed random-effects covariance](crossed-cov.md) `G` and `ε ~ N(0, σ_e² I)`. For a fixed-effects
design `X` with rows `I × J` and columns `p` and coefficients `β ∈ ℝ^p`, let `Y = X β + Z γ + ε`,
with `Z` the [crossed design](crossed-design.md). Then for all observations `(i, j)` and `(i', j')`,

`Cov(Y_{(i,j)}, Y_{(i',j')}) = [i = i'] σ_s² + [j = j'] σ_w² + [(i, j) = (i', j')] σ_e²`,

where `[·]` is `1` if the condition holds and `0` otherwise. This is the
[covariance of the mixed-model response](../../../Biology/quantitative-genetics/linear-mixed-models-and-blup/covariance-mixed-model-response.md),
`Z G Zᵀ + σ_e² I`, with its [entries](phen-cov-crossed-apply.md) computed.
