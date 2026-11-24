# Blasius force (iρ/2) ∮ W² dz on the circle of radius R about 0

For a real `ρ`, a function `W : ℂ → ℂ` and a real `R`, the Blasius force is `F = (iρ/2) ∮ W(z)² dz`,
the integral being taken once counterclockwise around the circle of radius `|R|` centred at `0`,
parametrised by `z = R e^{iθ}`, `0 ≤ θ ≤ 2π`. For `R = 0` it is `0`; a negative `R` gives the same
value as `|R|`; and if `θ ↦ W(R e^{iθ})²` is not integrable on `0 ≤ θ ≤ 2π`, the integral, and so
`F`, is `0` by convention. The intended inputs are a density `ρ > 0`, a radius `R > 0` and a complex
velocity `W = u − iv` continuous on the circle.

Blasius' theorem identifies this integral, taken around a body in a steady two-dimensional
irrotational incompressible flow, with the force per unit span `F_x − i F_y` on the body. Here the
expression is a definition; its agreement with a surface-pressure force is proved for the
[cylinder at zero angle of attack](blasius-force-eq-surface-force.md).
