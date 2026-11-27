# Body coordinates of a point given in inertial coordinates

For a point `o ∈ ℝ³`, the inertial coordinates of the origin of a body frame, an orientation
`R ∈ SO(3)` and inertial coordinates `x_I ∈ ℝ³`, the body coordinates of the point are
`x_B = Rᵀ (x_I - o)`. This map [inverts](inertial-to-body-body-to-inertial.md) the map
[`x_B ↦ o + R x_B`](body-to-inertial.md).
