# Each link is a body frame rotated by its absolute angle

For all real `l₁`, `l₂`, `q₁` and `q₂`, with the plane of the pendulum embedded as the first two
coordinates of `ℝ³` ([embedding](to-space.md)):

- the first mass is at `R(q₁) (0, -l₁, 0)`, the
  [inertial coordinates](../body-fixed-and-inertial-frames/body-to-inertial.md) of the body point
  `(0, -l₁, 0)` of the frame with origin `0` and orientation `R(q₁)`;
- the second mass is at `p₁ + R(q₂) (0, -l₂, 0)`, the inertial coordinates of the body point
  `(0, -l₂, 0)` of the frame with origin the first mass `p₁` and orientation `R(q₂)`.

Here `R(θ)` is the
[rotation by `θ` about the third axis](../body-fixed-and-inertial-frames/rot-z.md), with rows
`(cos θ, -sin θ, 0)`, `(sin θ, cos θ, 0)` and `(0, 0, 1)`. Both orientations are absolute: the
second link is rotated by `q₂`, not by `q₂ - q₁`, relative to the inertial axes.
