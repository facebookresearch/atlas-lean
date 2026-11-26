# Cluster-mean variance as design effect times independent-row variance

Let `m` be a natural number, `p` a finite index type, `P` a probability measure on a space `Ω`, and
`σ_c², σ_w² ≥ 0`. Let `γ : Ω → ℝ¹` and `ε : Ω → ℝ^m` be measurable and independent, with
`γ ~ N(0, σ_c²)` and `ε ~ N(0, σ_w² I_m)`. For a fixed-effects design `X` of size `m × p` and
`β ∈ ℝ^p`, let `Y = X β + 𝟙 γ + ε`, with `𝟙` the [all-ones design](cluster-design.md): one cluster
of `m` observations sharing the effect `γ`. If `m ≥ 1`, then for every observation `k`, the mean
`Ȳ = (Y_0 + ⋯ + Y_{m-1}) / m` satisfies `Var(Ȳ) = (1 + (m - 1) ρ) Var(Y_k) / m`, where
`ρ = σ_c² / (σ_c² + σ_w²)` is the
[intraclass correlation](icc.md) and `1 + (m - 1) ρ`
the design effect: the variance of the mean is the design effect times the variance `Var(Y_k) / m`
the mean would have if the observations were independent. When `σ_c² = σ_w² = 0`, `ρ = 0 / 0` is
read as `0` and both sides are `0`.
