# Local cylindrical frame at azimuth φ, the rotation by φ about e₃

For a real azimuth `φ` (in radians), the local cylindrical frame at `φ` is the
[rotation](../../classical-mechanics/rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/rot-z.md)
by `φ` about the third axis, the element of `SO(3)` with the rows `(cos φ, -sin φ, 0)`,
`(sin φ, cos φ, 0)` and `(0, 0, 1)`. Its columns are the radial, tangential and axial unit vectors
`e_r = (cos φ, sin φ, 0)`, `e_θ = (-sin φ, cos φ, 0)` and `e₃ = (0, 0, 1)`. A positive `φ` turns
`e₁` towards `e₂`, counterclockwise seen from the tip of `e₃`, so `e_θ` points in the sense of
increasing azimuth. As the orientation of a body frame it maps cylindrical components
`(v_r, v_θ, v_z)` to the
[inertial components](../../classical-mechanics/rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/body-to-inertial-vec.md)
`v_r e_r + v_θ e_θ + v_z e₃`.
