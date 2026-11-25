# Blasius force (iρ/2) ∮ W² dz on the circle of radius R about 0

For a real `ρ`, a function `W : ℂ → ℂ` and a real `R`, the Blasius force is `F = (iρ/2) ∮ W(z)² dz`,
the integral being taken once counterclockwise around the circle of radius `|R|` centred at `0`,
parametrised by `z = R e^{iθ}`, `0 ≤ θ ≤ 2π`. For `R = 0` it is `0`, and if `θ ↦ W(R e^{iθ})²` is
not integrable on `0 ≤ θ ≤ 2π`, the integral, and so `F`, is `0` by convention. The intended inputs
are a density `ρ > 0`, a radius `R > 0` and a complex velocity `W = u − iv` continuous on the
circle.

It is the expression of Blasius' theorem for the force per unit span `F_x − i F_y` on a body in a
steady two-dimensional irrotational incompressible flow, taken here as a definition. Its agreement
with the surface-pressure force is proved for the [cylinder flow](circle-velocity.md) `w` at zero
angle of attack ([agreement](blasius-force-eq-surface-force.md)), for `ρ, a, U > 0`, the Bernoulli
pressure `p = p∞ + ρ (U² − ‖w‖²)/2` on `‖z‖ ≥ a` and a radius `R ≥ a`.
