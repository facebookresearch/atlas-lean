# The plant holds exactly when the inertial balance laws hold

Consider a rigid motion in three dimensions with mass `m`, centre-of-mass coordinates
`X(t) ∈ ℝ³`, orientation `R(t) ∈ SO(3)` and a body frame centred at its centre of mass,
[force and moment maps](force-moment-maps.md) with admitted domain `D`, a trajectory `x` of
states and `g ∈ ℝ³`. The [six-degree-of-freedom plant](six-dof-plant.md) holds at `t` exactly
when `m > 0`, every entry of `R` and every component of `X` is twice continuously differentiable
on some open set of times containing `t`, the state `x(t)` lies in `D`, and both inertial balance
laws hold at `t` with the force `F_B` and the moment `M_B` the maps give at `x(t)`:

`m X''(t) = R(t) F_B + m g` and `L'(t) = R(t) M_B`,

with `L` the
[angular momentum about the centre of mass](../../rigid-bodies-and-mechanisms/rigid-body-motion-angular-momentum-and-euler-s-e/com-angular-momentum.md).
