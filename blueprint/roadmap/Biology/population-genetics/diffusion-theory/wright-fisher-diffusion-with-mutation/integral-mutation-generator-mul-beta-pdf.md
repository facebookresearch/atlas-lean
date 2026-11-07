# Weak stationarity of Wright's law (density form)

For `θ₁, θ₂ > 0` and every `f` twice
continuously differentiable on `[0, 1]`, `∫₀¹ (L f)(x) π(x) dx = 0` for the Beta`(θ₁, θ₂)`
density `π`. (`L f` uses `deriv`, which agrees with the one-sided derivatives inside `(0, 1)`;
its values at the endpoints do not affect the integral.) The proof is integration by parts:
`L f · π = (x ^ θ₁ (1 - x) ^ θ₂ f' / (2 B(θ₁, θ₂)))'` on `(0, 1)` because the flux vanishes, and
this boundary term is `0` at both endpoints since `θ₁, θ₂ > 0`.
