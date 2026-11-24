# Dividing a master-equation solution by a constant gives a solution

Let `N` be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set `S` and finite reaction set `ρ`, and let `κ ∈ ℝ^ρ` be rate constants of any sign.
If `p : ℕ^S → ℝ` solves the
[stationary master equation](../ergodic-theorem-for-complex-balanced-reaction-ne/is-stationary-master-solution.md)
for `κ`, then so does `x ↦ p(x) / a` for every real `a`, since the equation is linear in `p`. For
`a = 0` the convention `y / 0 = 0` makes it the zero function, which is a solution as well.
