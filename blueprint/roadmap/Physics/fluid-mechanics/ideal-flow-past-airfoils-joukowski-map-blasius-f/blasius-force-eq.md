# Blasius force iρUΓ e^(−iα) from a far-field expansion of the velocity

Let `ρ > 0`, `U > 0` and `0 < R₀ < R₁`, and let `Γ`, `α`, `K` be real. Let `W` and `e` be functions
from `ℂ` to `ℂ` such that `W` is complex differentiable on the region `‖z‖ > R₀` and, for every `z`
with `‖z‖ ≥ R₁`:

- `W(z) = U e^{−iα} + Γ/(2πi z) + e(z)`;
- `e` is complex differentiable at `z`;
- `‖e(z)‖ ≤ K/‖z‖²`.

Then for every radius `R > R₀` the [Blasius force](blasius-force.md) of `W` with density `ρ` is
`(iρ/2) ∮ W(z)² dz = iρUΓ e^{−iα}`, the integral taken counterclockwise around the circle `‖z‖ = R`.
The value does not depend on `R`, since `W²` is holomorphic between any two such circles; for large
`R` only the cross term between the free stream and the vortex term contributes.

Read as `F_x − i F_y`, the force is `F_x = ρUΓ sin α`, `F_y = −ρUΓ cos α`: of magnitude `ρU|Γ|`,
perpendicular to the free-stream direction `(cos α, sin α)` (no drag), with
[signed lift](signed-lift.md) `−ρUΓ`. This is the Kutta–Joukowski force in complex form, under the
hypotheses above.
