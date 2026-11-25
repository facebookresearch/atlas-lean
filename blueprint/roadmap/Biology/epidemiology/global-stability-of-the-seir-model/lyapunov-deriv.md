# Lyapunov derivative for the endemic equilibrium

For real parameters `β, σ, γ, μ, N` and real `S, E, I`, with the endemic levels
[`S*`](endemic-s.md), [`E*`](endemic-e.md) and [`I*`](endemic-i.md),

`V̇(S, E, I) = −μ (S − S*)² / S − (β S* I* / N) (S* / S + S I E* / (S* I* E) + E I* / (E* I) − 3)`,

with the convention `x / 0 = 0` in every quotient. Under `σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0` and
`R₀ > 1`, where `R₀` is the [basic reproduction number](r0.md) `R₀ = β σ / ((μ + σ) (μ + γ))`, it is
the derivative of the [Lyapunov function](lyapunov.md) `V`
[along solutions](has-deriv-at-lyapunov.md) at times `t ≥ 0` with `S(t), E(t), I(t) > 0`.
