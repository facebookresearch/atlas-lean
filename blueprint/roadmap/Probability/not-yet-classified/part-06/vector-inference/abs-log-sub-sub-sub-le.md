# Second-order expansion of the log-likelihood

**Second-order expansion of the log-likelihood** of one observation. If on the ball of
radius `δ` about `θ₀` the log-density `θ ↦ log p θ x` is differentiable (so `score p θ x` is
its true gradient) and the score is differentiable with
`‖Dscore θ x - Dscore θ₀ x‖ ≤ C ‖θ - θ₀‖`, then for `θ` in the ball
`|log p θ x - log p θ₀ x - ⟪score p θ₀ x, θ - θ₀⟫ - ⟪Dscore θ₀ x (θ - θ₀), θ - θ₀⟫ / 2|
  ≤ C ‖θ - θ₀‖³`.
