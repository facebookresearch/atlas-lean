# Rotation-matrix kinematics with the rate multiplied on the left

Let `q` be a quaternion-valued function of time, `ω` a function of time with values in `ℝ³`, and
`t` a time at which `q'(t) = (1/2) (0, ω(t)) q(t)`, the rate entering as a
[pure quaternion](pure-quat.md) multiplied on the left. For a quaternion `p`, let `R(p)` be the
matrix, in the basis `i, j, k`, of the linear map `v ↦ p v p⋆` on pure quaternions (`p⋆` the
conjugate of `p`). Then `s ↦ R(q(s))` has, entry by entry, the derivative

`[ω(t)]ₓ R(q(t))`

at `t`, where `[ω]ₓ` is the cross-product matrix, `[ω]ₓ v = ω × v`. No unit-norm hypothesis is
needed. This is a different frame convention from the
[body-rate kinematics](has-deriv-at-rot-matrix.md), where the rate multiplies on the right and
`R' = R [ω_B]ₓ`: here `ω` has inertial components, and when `|q(t)| = 1`, so that `R(q(t))` is a
rotation matrix, `R' Rᵀ = [ω]ₓ` at `t`.
