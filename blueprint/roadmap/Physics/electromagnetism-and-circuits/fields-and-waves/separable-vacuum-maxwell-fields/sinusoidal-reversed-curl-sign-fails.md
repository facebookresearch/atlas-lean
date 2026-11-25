# The sign-reversed formula for the x component of B fails

Let `c > 0` be the speed of light and `A` the
[sinusoidal guide potential](sinusoidal-guide-potential.md), with vector potential
`(0, sin x cos(2t - 3z), 0)` and scalar potential `0`. It is not true that
`B_x(t, x, y, z) = sin x ∂f/∂z(t, z)` for all `t` and `(x, y, z)`, with `f(t, z) = cos(2t - 3z)`:
the [magnetic field](sinusoidal-magnetic-field.md) has `B_x = -sin x ∂f/∂z`, and at time `0` and
position `(π/2, 0, -π/6)` the two sides are `-3` and `3`.
