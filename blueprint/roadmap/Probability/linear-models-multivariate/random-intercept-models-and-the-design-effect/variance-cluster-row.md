# Variance of each observation of a Gaussian single-cluster response

Let `m` be a natural number, `p` a finite index type, `P` a probability measure on a space `Ω`, and
`σ_c², σ_w² ≥ 0`. Let `γ : Ω → ℝ¹` and `ε : Ω → ℝ^m` be measurable and independent, with
`γ ~ N(0, σ_c²)` and `ε ~ N(0, σ_w² I_m)`. For a fixed-effects design `X` of size `m × p` and
`β ∈ ℝ^p`, let `Y = X β + 𝟙 γ + ε`, with `𝟙` the [all-ones design](cluster-design.md): one cluster
of `m` observations sharing the effect `γ`. Then every observation has variance
`Var(Y_k) = σ_c² + σ_w²`, `k ∈ {0, …, m - 1}`.
