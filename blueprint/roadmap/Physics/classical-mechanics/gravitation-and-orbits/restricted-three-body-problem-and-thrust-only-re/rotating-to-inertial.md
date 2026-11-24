# Inertial coordinates of a point given in rotating coordinates

For a real triple `ξ = (ξ₁, ξ₂, ξ₃)` of rotating-frame coordinates and a time `t`, the inertial
coordinates of the point are `X = R(t) ξ = (ξ₁ cos t - ξ₂ sin t, ξ₁ sin t + ξ₂ cos t, ξ₃)`, where
`R(t)` is the [orientation of the rotating frame](rotating-frame.md), the rotation by the angle
`t` about the third axis. This is the
[body-to-inertial map](../../rigid-bodies-and-mechanisms/body-fixed-and-inertial-frames/body-to-inertial.md)
`x_I = o + R x_B` with origin `o = 0`: both frames have their origin at the barycenter of the
primaries.
