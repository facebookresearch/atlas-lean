# For a unit quaternion the vee of Rᵀ R' is the body rate

Let `q` be a quaternion-valued function of time, `ω_B` a function of time with values in `ℝ³`,
and `t` a time with `|q(t)| = 1` at which `q'(t) = (1/2) q(t) (0, ω_B(t))`, the body rate entering
as a [pure quaternion](pure-quat.md) multiplied on the right. Let `R(s)` be the matrix, in the
basis `i, j, k`, of the linear map `v ↦ q(s) v q(s)⋆` on pure quaternions (`q(s)⋆` the conjugate),
and `R'(t)` its derivative at `t`, taken entry by entry. Then

`vee(R(t)ᵀ R'(t)) = ω_B(t)`,

where the vee of a `3 × 3` matrix `A`, with rows and columns indexed from `0`, is
`(A₂₁, A₀₂, A₁₀)`; it recovers `ω` from the cross-product matrix `[ω]ₓ`, `[ω]ₓ v = ω × v`. So the
body rate of the quaternion kinematics is the body angular velocity read off the attitude matrix.
