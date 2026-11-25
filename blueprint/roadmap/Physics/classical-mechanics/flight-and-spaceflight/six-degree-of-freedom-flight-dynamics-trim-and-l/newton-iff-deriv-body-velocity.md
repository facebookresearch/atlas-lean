# Newton's law in inertial axes is the body-axis translational equation

Consider a rigid motion in three dimensions of positive mass `m > 0`, with centre-of-mass
coordinates `X(t) ∈ ℝ³` and orientation `R(t) ∈ SO(3)` (body-to-inertial convention
`v_I = R v_B`). Let `U` be an open set of times on which every entry of `R` and every component of
`X` is twice continuously differentiable, let `F_B` and `g` be vectors of `ℝ³`, and let `t ∈ U`.
Then the inertial law

`m X''(t) = R(t) F_B + m g`

holds exactly when the body equation

`v_B'(t) = F_B / m + R(t)ᵀ g − ω_B(t) × v_B(t)`

holds, where `v_B = Rᵀ X'` is the [body velocity](body-velocity.md) and `ω_B` the body angular
velocity, the vee of `Rᵀ R'`. Here `F_B` is the force in body components and `g` the uniform
gravitational acceleration in inertial components. The proof uses the
[transport law](../../rigid-bodies-and-mechanisms/rigid-body-motion-angular-momentum-and-euler-s-e/deriv-body-to-inertial-vec.md)
`d(R u)/dt = R (u' + ω_B × u)`.
