# Axial component of the rotational balance law

Let `M` be a rigid-body motion in three dimensions (a rigid body with a mass distribution, a
centre-of-mass trajectory and an orientation `s ↦ R(s) ∈ SO(3)`) whose body frame is centred at
the centre of mass, let `U` be an open set of times on which every entry of `R` is twice
continuously differentiable and the body angular velocity is `(0, 0, ω(s))`, and let `t ∈ U`. If
the [angular momentum about the centre of mass](../../rigid-bodies-and-mechanisms/rigid-body-motion-angular-momentum-and-euler-s-e/com-angular-momentum.md) has derivative
`τ_I ∈ ℝ³` at `t` (the rotational balance law with inertial torque `τ_I`), then

`J ω'(t) = (Rᵀ τ_I)₃`,

where `J` is the diagonal entry of the inertia tensor about the centre of mass for the third axis,
`R = R(t)`, `Rᵀ τ_I` gives the body components of the torque, and `ω'` is the derivative of `ω`
(taken to be `0` where `ω` is not differentiable, like the derivative of the angular momentum).
