# Pitch orientation as a rotation about the third axis

For a pitch angle `θ`, the pitch orientation is the
[rotation by `θ` about the third axis](../../rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/rot-z.md)

`Rz(θ) = [[cos θ, −sin θ, 0], [sin θ, cos θ, 0], [0, 0, 1]]`,

an element of `SO(3)`. With the first two axes spanning the forward/up plane, `θ > 0` turns the
body forward axis `Rz(θ) e₁ = (cos θ, sin θ, 0)` from forward toward up (nose up).
