# Lyapunov function of the disease-free equilibrium

For real `σ, μ, N` and real `S, E, I`, `V₀(S, E, I) = g(N, S) + E + ((μ + σ) / σ) I`, where `g` is
the [Volterra function](volterra.md) `g(a, x) = x − a − a log(x / a)`; with the convention
`x / 0 = 0`, the coefficient `(μ + σ) / σ` is `0` when `σ = 0`, and `g` uses `log 0 = 0` and
`log y = log |y|`. The intended domain is `S > 0`, `N > 0` and `σ > 0`.
