# Rate of a rotated vector under body-rate quaternion kinematics

Let `q` be a quaternion-valued function of time, `ω_B` a function of time with values in `ℝ³`,
and `t` a time at which `q` has the derivative

`q'(t) = (1/2) q(t) (0, ω_B(t))`,

the body rate entering as a [pure quaternion](pure-quat.md) multiplied on the right. For a
quaternion `p`, let `R(p)` be the matrix, in the basis `i, j, k`, of the linear map `v ↦ p v p⋆`
on pure quaternions, where `p⋆` is the conjugate of `p`; for `|p| = 1` it is the rotation matrix
of `p`. Then for every vector `v ∈ ℝ³` the function `s ↦ R(q(s)) v` has the derivative

`R(q(t)) (ω_B(t) × v)`

at `t`. No unit-norm hypothesis on `q` is needed. In rigid-body terms, `ω_B` is the angular
velocity in body components: `R' v = R (ω_B × v)`.
