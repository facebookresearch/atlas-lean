# Six-degree-of-freedom plant defined by force and moment maps

Consider a rigid motion in three dimensions with mass `m`, centre-of-mass coordinates
`X(t) ∈ ℝ³` and orientation `R(t) ∈ SO(3)`, [force and moment maps](force-moment-maps.md) with
admitted domain `D`, a trajectory `x` of states, the state the maps read, and the uniform
gravitational acceleration `g ∈ ℝ³`. The six-degree-of-freedom plant holds at time `t` when

- the mass is positive, `m > 0`;
- on some open set of times containing `t`, every entry of `R` and every component of `X` is
  twice continuously differentiable;
- the state is admitted, `x(t) ∈ D`, and the
  [six-degree-of-freedom body equations](six-dof-body-equations.md) hold at `t` with the force
  and the moment the maps give at `x(t)`.

Positive mass keeps the force in the translational equation, and the regularity makes the time
derivatives in the body equations genuine derivatives.
