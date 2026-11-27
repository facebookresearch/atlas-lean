# Sup-norm bounds on the remainder near the trim

Let `0 < r ≤ 1/100`, and let `δ = (x, z, θ, q) ∈ ℝ⁴` have every coordinate at most `r` in
absolute value. Then `δ` lies in the [actuator box](actuator-box.md), and with `‖δ‖` the sup norm
the components of the [nonlinear remainder](longitudinal-remainder.md)
`N(δ) = (−x³, 0, 0, θ − sin θ)` satisfy

`|−x³| ≤ r ‖δ‖²`, `N₂ = N₃ = 0` for the middle components, and `|θ − sin θ| ≤ (r / 6) ‖δ‖²`,

the last by the cubic bound `|θ − sin θ| ≤ |θ|³ / 6`.
