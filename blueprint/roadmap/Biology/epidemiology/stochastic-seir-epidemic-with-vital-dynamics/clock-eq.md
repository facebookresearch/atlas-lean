# Internal clocks in scaled form

For real parameters `β`, `σ`, `γ`, `μ`, every `N ∈ ℕ`, count paths `S, E, I, R : ℝ → ℕ`, every
[channel](channel.md) `c` and every time `t`, the [internal clock](clock.md) is

`A_c(t) = max(N ∫₀ᵗ λ_c(S(x) / N, E(x) / N, I(x) / N, R(x) / N) dx, 0)`,

with `λ_c` the [scaled intensity](scaled-rate.md).
