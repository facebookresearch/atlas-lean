# Orientation of the frame rotating with the primaries

For a time `t`, the orientation of the frame that rotates with the primaries is the
[rotation about the third axis](../../rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/rot-z.md)
by the angle `t`, as an element of `SO(3)`: the matrix `R(t)` with rows `(cos t, -sin t, 0)`,
`(sin t, cos t, 0)` and `(0, 0, 1)`, so `R(0)` is the identity. In the
[body-to-inertial convention](../../rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/body-to-inertial.md)
`x_I = o + R x_B` its columns are the rotating axes in inertial components: the first rotating
axis is `(cos t, sin t, 0)`, and the frame turns counterclockwise, seen from the positive third
axis, at unit angular speed (angular velocity `e₃`) in the normalized units of the model.
