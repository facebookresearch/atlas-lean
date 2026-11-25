# Forward-global solutions for nonnegative rates and data

For `β, σ, γ, μ, N ≥ 0` and initial values `s₀, e₀, i₀, r₀ ≥ 0`, there are functions
`S, E, I, R : ℝ → ℝ` forming a [solution](is-solution.md) with `S(0) = s₀`, `E(0) = e₀`,
`I(0) = i₀`, `R(0) = r₀`, such that `S(t), E(t), I(t), R(t) ≥ 0` and
`S(t) + E(t) + I(t) + R(t) ≤ max(N, s₀ + e₀ + i₀ + r₀)` for every `t ≥ 0`. The closed model `μ = 0`
is included, and so is `N = 0`, where the infection term `β S I / N` is `0` by the convention
`x / 0 = 0`.
