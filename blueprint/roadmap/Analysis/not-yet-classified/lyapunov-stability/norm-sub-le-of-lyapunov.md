# Lyapunov's direct method, exponential decay of the state

In addition to the hypotheses
of `lyapunov_le_exp`, assume the quadratic comparison bounds
`c₁ ‖x - x₀‖² ≤ V x ≤ c₂ ‖x - x₀‖²` on `s` with `c₁ > 0`. Then for every `t ≥ 0`,
`‖γ t - x₀‖ ≤ √(c₂ / c₁) * exp (-(a / 2) * t) * ‖γ 0 - x₀‖`.
