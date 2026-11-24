# The cylinder's Blasius force equals its Bernoulli pressure force

Let `ρ > 0`, `a > 0`, `U > 0` and `R ≥ a`, let `p∞` and `Γ` be real, and let `p : ℂ → ℝ` satisfy
Bernoulli's law in the flow region: `p(z) = p∞ + ρ(U² − ‖w(z)‖²)/2` for every `z` with `‖z‖ ≥ a`,
where `w` is the [circle velocity](circle-velocity.md) at angle of attack `0`. Then the
[Blasius force](blasius-force.md) of `w`, with density `ρ` and at radius `R`, equals `F_x − i F_y`
for the surface-pressure force `(F_x, F_y)` on the cylinder `r = a`, given by the
[horizontal](surface-force-x.md) and [vertical](surface-force-y.md) pressure-force integrals: both
are `iρUΓ` ([Blasius force](blasius-force-circle-velocity-zero.md),
[pressure force](surface-force-eq.md)).

This checks the Blasius contour force against the pressure integral for the circular cylinder at
zero angle of attack. The pressure integrands are integrable
([integrability](surface-pressure-interval-integrable.md)), so no convention for non-integrable
functions enters the comparison.
