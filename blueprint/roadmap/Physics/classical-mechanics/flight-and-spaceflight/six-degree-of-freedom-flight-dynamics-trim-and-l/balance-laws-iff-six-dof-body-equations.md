# Inertial balance laws are equivalent to the body equations

Consider a rigid motion in three dimensions of positive mass `m > 0`, with centre-of-mass
coordinates `X(t) ∈ ℝ³`, orientation `R(t) ∈ SO(3)` and a body frame centred at its centre of
mass. Let `U` be an open set of times on which every entry of `R` and every component of `X` is
twice continuously differentiable, let `g`, `F_B` and `M_B` be vectors of `ℝ³`, and let `t ∈ U`.
Then the translational law `m X''(t) = R(t) F_B + m g` and the rotational law `L'(t) = R(t) M_B`,
with `L` the
[angular momentum about the centre of mass](../../rigid-bodies-and-mechanisms/rigid-body-motion-angular-momentum-and-euler-s-e/com-angular-momentum.md),
both hold exactly when the [six-degree-of-freedom body equations](six-dof-body-equations.md) hold
at `t`:

`v_B'(t) = F_B / m + R(t)ᵀ g − ω_B(t) × v_B(t)` and
`I_B ω_B'(t) + ω_B(t) × (I_B ω_B(t)) = M_B`.
