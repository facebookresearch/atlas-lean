# Disease-free Lyapunov derivative

For real `β, σ, γ, μ, N` and real `S, I`,
`V̇₀(S, I) = −μ (S − N)² / S + (β − (μ + σ) (μ + γ) / σ) I`, with the convention `x / 0 = 0`: the
first term is `0` when `S = 0`, and the quotient in the coefficient is `0` when `σ = 0`. For
`σ > 0`, `γ ≥ 0` and `μ > 0` the coefficient of `I` is `((μ + σ) (μ + γ) / σ) (R₀ − 1)`, with `R₀`
the [basic reproduction number](r0.md). For `σ ≠ 0` and `N ≠ 0`, it is the derivative of the
[disease-free Lyapunov function](dfe-lyapunov.md) `V₀`
[along solutions](has-deriv-at-dfe-lyapunov.md) at times `t ≥ 0` with `S(t) ≠ 0`.
