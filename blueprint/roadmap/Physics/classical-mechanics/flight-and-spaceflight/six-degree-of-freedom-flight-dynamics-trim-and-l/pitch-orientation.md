# Rotation about the third axis as a pitch or rotating-frame orientation

For a pitch angle `θ`, the pitch orientation is the
[rotation by `θ` about the third axis](../../rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/rot-z.md)

`Rz(θ) = [[cos θ, −sin θ, 0], [sin θ, cos θ, 0], [0, 0, 1]]`,

an element of `SO(3)`. With the first two axes spanning the forward/up plane, `θ > 0` turns the
body forward axis `Rz(θ) e₁ = (cos θ, sin θ, 0)` from forward toward up (nose up).

The same rotation, with a time `t` as the angle, is the orientation of the frame that rotates with
the primaries in the restricted three-body problem: in the body-to-inertial convention
`x_I = o + Rz(t) x_B` its columns are the rotating axes in inertial components, so the first
rotating axis is `(cos t, sin t, 0)` and the frame turns counterclockwise, seen from the positive
third axis, at unit angular speed in the normalized units of that model.
