# Intensities of the channels along count paths

For real parameters `β`, `σ`, `γ`, `μ`, a scale `N ∈ ℕ`, count paths `S, E, I, R : ℝ → ℕ`, a
[channel](channel.md) `c` and a time `x`, the intensity of `c` at time `x` in Kurtz's
density-dependent form

`rate_c(x) = N λ_c(S(x) / N, E(x) / N, I(x) / N, R(x) / N)`,

with `λ_c` the [scaled intensity](scaled-rate.md). For `N ≥ 1` these are `μ N`, `β S(x) I(x) / N`,
`σ E(x)`, `γ I(x)`, `μ S(x)`, `μ E(x)`, `μ I(x)` and `μ R(x)`; when `β, σ, γ, μ ≥ 0` they are the
jump rates of the chain. At `N = 0` division by zero gives `0`, and every intensity is `0`.
