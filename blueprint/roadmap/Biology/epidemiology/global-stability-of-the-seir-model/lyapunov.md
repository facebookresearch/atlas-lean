# Korobeinikov Lyapunov function of the endemic equilibrium

For real parameters `β, σ, γ, μ, N` and real `S, E, I`,
`V(S, E, I) = g(S*, S) + g(E*, E) + ((μ + σ) / σ) g(I*, I)`, where `g` is the
[Volterra function](volterra.md) `g(a, x) = x − a − a log(x / a)` and `S*`, `E*`, `I*` are the
[susceptible](endemic-s.md), [exposed](endemic-e.md) and [infectious](endemic-i.md) endemic levels;
with the convention `x / 0 = 0`, the coefficient `(μ + σ) / σ` is `0` when `σ = 0`, and `g` uses the
conventions `x / 0 = 0`, `log 0 = 0` and `log y = log |y|`, so `V` is finite, and can be negative,
off the open orthant `S, E, I > 0`. The intended domain is `σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0`,
`R₀ > 1` and `S, E, I > 0`, where `R₀` is the [basic reproduction number](r0.md).
