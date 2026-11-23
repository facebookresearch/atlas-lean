# Dfe Lyapunov Deriv

The derivative of `dfeLyapunov` along the vector field
(`IsSolution.hasDerivAt_dfeLyapunov`): `V̇₀ = -μ (S - N)² / S + (β - (μ + σ) (μ + γ) / σ) I`.
The coefficient of `I` is `((μ + σ) (μ + γ) / σ) (R₀ - 1)`. Meaningful for `S > 0` and
`σ > 0`, where it is the derivative; at `S = 0` or `σ = 0` Lean's division returns `0`.
