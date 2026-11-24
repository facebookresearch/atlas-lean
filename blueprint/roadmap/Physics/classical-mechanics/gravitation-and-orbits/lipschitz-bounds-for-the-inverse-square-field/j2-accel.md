# J2 Accel

The `J2` perturbing acceleration for gravitational parameter `μ`,
reference radius `R`, and signed oblateness coefficient `J2`, at a
position `r` in three-dimensional Euclidean space. With axial
coordinate `z = r 2` and `u = z^2 / ‖r‖^2`, and `ẑ = single 2 z` the
axial projection of `r`:
`a = -(3 * J2 * μ * R^2 / (2 * ‖r‖^5)) * ((1 - 5u) • r + 2 • ẑ)`.

Convention: this is the acceleration from the geopotential term
`-(μ / ‖r‖) * J2 * (R / ‖r‖)^2 * P₂(z / ‖r‖)` with Legendre
polynomial `P₂`, so positive `J2` is the oblate case (Earth:
`J2 ≈ 1.083e-3`); equivalently the negative of the gradient of the
full potential's `J2` part with the opposite geodetic sign
convention is not used. This matches the component formulas in
Vallado, *Fundamentals of Astrodynamics and Applications*. At
`r = 0` the scalar factor is Lean's junk value; the field is read
away from the origin.
