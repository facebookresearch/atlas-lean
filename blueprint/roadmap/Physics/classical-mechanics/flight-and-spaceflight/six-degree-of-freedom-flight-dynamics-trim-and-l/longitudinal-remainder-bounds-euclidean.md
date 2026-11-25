# Euclidean-norm bounds on the remainder near the trim

Let `0 < r ≤ 1/100`, and let the state `e = (x, z, θ, q) ∈ ℝ⁴` have Euclidean norm `‖e‖ ≤ r`.
Then its coordinates lie in the [actuator box](actuator-box.md), and the components of the
[nonlinear remainder](longitudinal-remainder.md) `N(e) = (−x³, 0, 0, θ − sin θ)` satisfy

`|−x³| ≤ r ‖e‖²`, `N₂ = N₃ = 0` for the middle components, and `|θ − sin θ| ≤ (r / 6) ‖e‖²`:

the [sup-norm bounds](longitudinal-remainder-bounds.md) through `‖e‖_∞ ≤ ‖e‖`.
