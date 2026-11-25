# The rigid-body displacement follows the body-to-inertial convention

Let `M` be a rigid-body motion in three dimensions: a rigid body with centre of mass `c`, a
centre-of-mass trajectory `t ↦ o(t)` in the inertial frame and an orientation `t ↦ R(t) ∈ SO(3)`.
At every time `t` and for every body point `y`, the rigid displacement of `M` at `t` maps `y` to
`o(t) + R(t) (y - c)`, the [inertial coordinates](body-to-inertial.md) of the point with body
coordinates `x_B = y - c` in the frame with origin `o(t)` and orientation `R(t)`.
