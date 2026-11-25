# For c > 0, the integral damper equation is the Langevin equation

Let `c > 0`, let `k`, `σ` and `x₀` be real numbers, `x, w : ℝ → ℝ` and `t` a time. Then

`c (x(t) - x₀) = -k ∫₀ᵗ x(u) du + σ (w(t) - w(0))`

holds if and only if

`x(t) = x₀ - (k / c) ∫₀ᵗ x(u) du + (σ / c) (w(t) - w(0))`,

the integral form of the Langevin equation with rate `θ = k / c` and noise amplitude
`σ' = σ / c`. The integral is oriented and taken to be `0` when `x` is not integrable on the
interval; the same integral appears on both sides.
