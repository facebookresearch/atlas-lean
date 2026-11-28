# The Gaussian cluster response is a random-intercept model

Let `m` be a natural number, `p` a finite index type, `P` a probability measure on a space `Ω`, and
`σ_c², σ_w² ≥ 0`. Let `γ : Ω → ℝ¹` and `ε : Ω → ℝ^m` be measurable and independent, with
`γ ~ N(0, σ_c²)` and `ε ~ N(0, σ_w² I_m)`. For a fixed-effects design `X` of size `m × p` and
`β ∈ ℝ^p`, let `Y = X β + 𝟙 γ + ε`, with `𝟙` the [all-ones design](cluster-design.md): one cluster
of `m` observations sharing the effect `γ`. Indexing the observations by `{0} × {0, …, m - 1}` (one
donor, `m` cells), `Y` is a
[random-intercept model](is-random-intercept.md) with
donor variance `σ_c²` and residual variance `σ_w²`: both variances are nonnegative, every `Y_k` is
square integrable, and `Cov(Y_k, Y_l) = σ_c² + [k = l] σ_w²`, where `[k = l]` is `1` if `k = l` and
`0` otherwise. The second-moment results for random-intercept models therefore apply to this
response.
