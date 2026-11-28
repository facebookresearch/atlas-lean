# Each Volterra term is bounded by the Lyapunov function on the open orthant

Under `σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0` and `R₀ > 1`, where `R₀` is the
[basic reproduction number](r0.md) `R₀ = β σ / ((μ + σ) (μ + γ))`, for all `S, E, I > 0` the
[Lyapunov function](lyapunov.md) `V` bounds each of its Volterra terms: `g(S*, S) ≤ V(S, E, I)`,
`g(E*, E) ≤ V(S, E, I)` and `g(I*, I) ≤ V(S, E, I)`, where `g` is the
[Volterra function](volterra.md) `g(a, x) = x − a − a log(x / a)`.
