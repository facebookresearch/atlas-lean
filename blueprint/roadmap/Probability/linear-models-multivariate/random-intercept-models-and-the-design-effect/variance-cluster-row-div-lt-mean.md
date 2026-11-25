# For m ≥ 2 and positive shared variance, naive mean variance is too low

Let `m` be a natural number, `p` a finite index type, `P` a probability measure on a space `Ω`,
`σ_c² > 0` and `σ_w² ≥ 0`. Let `γ : Ω → ℝ¹` and `ε : Ω → ℝ^m` be measurable and independent, with
`γ ~ N(0, σ_c²)` and `ε ~ N(0, σ_w² I_m)`. For a fixed-effects design `X` of size `m × p` and
`β ∈ ℝ^p`, let `Y = X β + 𝟙 γ + ε`, with `𝟙` the [all-ones design](cluster-design.md): one cluster
of `m` observations sharing the effect `γ`. If `m ≥ 2`, then for every observation `k`,
`Var(Y_k) / m < Var(Ȳ)`, where `Ȳ = (Y_0 + ⋯ + Y_{m-1}) / m`: the variance `Var(Y_k) / m` that the
mean would have if the observations were independent is strictly smaller than its true variance.
