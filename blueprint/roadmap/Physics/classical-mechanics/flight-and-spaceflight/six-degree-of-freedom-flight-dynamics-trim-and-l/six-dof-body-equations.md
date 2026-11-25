# Six-degree-of-freedom body equations of a rigid motion

Consider a rigid motion in three dimensions: a mass distribution with mass `m` and inertia tensor
`I_B` about its centre of mass, the centre-of-mass coordinates `X(t) ∈ ℝ³` and the orientation
`R(t) ∈ SO(3)` (body-to-inertial convention `v_I = R v_B`). For vectors `g`, `F_B` and `M_B` of
`ℝ³`, the uniform gravitational acceleration in inertial components, the body force and the body
moment about the centre of mass, the six-degree-of-freedom body equations hold at time `t` when

`v_B'(t) = m⁻¹ F_B + R(t)ᵀ g − ω_B(t) × v_B(t)` and
`I_B ω_B'(t) + ω_B(t) × (I_B ω_B(t)) = M_B`:

the translational body equation for the [body velocity](body-velocity.md) `v_B = Rᵀ X'`, and
[Euler's equations](../../rigid-bodies-and-mechanisms/rigid-body-motion-angular-momentum-and-euler-s-e/deriv-com-angular-momentum-eq-iff-euler.md)
for the body angular velocity `ω_B`, the vee of `Rᵀ R'`. Time derivatives are total, taken as `0`
at a time where the curve is not differentiable, and with the convention `0⁻¹ = 0` the force drops
out of the translational equation when `m = 0`. The intended domain is positive mass and twice
continuously differentiable data, as in the [six-degree-of-freedom plant](six-dof-plant.md).
