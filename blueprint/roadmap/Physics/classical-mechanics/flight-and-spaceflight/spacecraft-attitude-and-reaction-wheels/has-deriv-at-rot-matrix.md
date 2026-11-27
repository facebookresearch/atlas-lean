# Rotation-matrix kinematics from body-rate quaternion kinematics

Let `q` be a quaternion-valued function of time, `ω_B` a function of time with values in `ℝ³`,
and `t` a time at which `q'(t) = (1/2) q(t) (0, ω_B(t))`, the body rate entering as a
[pure quaternion](pure-quat.md) multiplied on the right. For a quaternion `p`, let `R(p)` be the
matrix, in the basis `i, j, k`, of the linear map `v ↦ p v p⋆` on pure quaternions (`p⋆` the
conjugate of `p`). Then the matrix-valued function `s ↦ R(q(s))` has, entry by entry, the
derivative

`R(q(t)) [ω_B(t)]ₓ`

at `t`, where `[ω]ₓ` is the cross-product matrix with rows `(0, −ω₂, ω₁)`, `(ω₂, 0, −ω₀)` and
`(−ω₁, ω₀, 0)`, so that `[ω]ₓ v = ω × v`. No unit-norm hypothesis on `q` is needed.
