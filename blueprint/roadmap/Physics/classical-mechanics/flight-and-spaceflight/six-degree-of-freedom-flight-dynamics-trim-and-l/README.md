# Six-degree-of-freedom flight dynamics, trim and linearization

## Body velocity and the translational correspondence

- [Body components of the centre-of-mass velocity](body-velocity.md)
- [With C² attitude and trajectory the body velocity is differentiable](differentiable-at-body-velocity.md)
- [Newton's law in inertial axes is the body-axis translational equation](newton-iff-deriv-body-velocity.md)

## The six-degree-of-freedom body equations

- [Six-degree-of-freedom body equations of a rigid motion](six-dof-body-equations.md)
- [Inertial balance laws are equivalent to the body equations](balance-laws-iff-six-dof-body-equations.md)

## Coefficient maps with admitted domains

- [Force and moment maps on an admitted state domain](force-moment-maps.md)
- [Six-degree-of-freedom plant defined by force and moment maps](six-dof-plant.md)
- [The plant holds exactly when the inertial balance laws hold](six-dof-plant-iff.md)

## A controlled longitudinal fixture

- [Lift coefficient of the longitudinal fixture](lift-coeff.md)
- [Drag polar of the longitudinal fixture](drag-coeff.md)
- [Flight speed of the longitudinal fixture](flight-speed.md)
- [Lift force of the longitudinal fixture](lift-force.md)
- [Drag force of the longitudinal fixture](drag-force.md)
- [Aerodynamic force of the longitudinal fixture](aero-force.md)
- [Ideal force actuator of the longitudinal fixture](actuator-force.md)
- [Pitch-moment actuator of the longitudinal fixture](pitch-moment.md)
- [Reduced longitudinal vector field](reduced-field.md)
- [Admitted actuator box of the longitudinal fixture](actuator-box.md)
- [Pitch orientation as a rotation about the third axis](pitch-orientation.md)
- [Longitudinal force and moment maps on the actuator box](longitudinal-maps.md)
- [Planar longitudinal motion of a rigid body](planar-motion.md)
- [Longitudinal state of a planar motion](planar-state.md)
- [The drag polar gives a drag coefficient of 3/10](drag-coeff-eq.md)
- [Lift is perpendicular to the velocity and drag opposes it](lift-force-drag-force-spec.md)
- [Aerodynamic, actuator and weight forces add up to the reduced force](aero-force-add-actuator-force-add-weight.md)
- [On planar motions the plant is the reduced field on the box](planar-six-dof-plant-iff.md)
- [The trim is a relative equilibrium](trim-relative-equilibrium.md)
- [Speed and actuator bounds on the actuator box](actuator-box-bounds.md)
- [Zero-speed states lie outside the box, where the plant fails](longitudinal-maps-rejects.md)

## Linearization about the trim

- [Jacobian of the reduced field at the trim](longitudinal-jacobian.md)
- [Nonlinear remainder of the reduced field about the trim](longitudinal-remainder.md)
- [The trim Jacobian is block diagonal](longitudinal-jacobian-eq-from-blocks.md)
- [The reduced field has derivative A at the trim](has-fderiv-at-reduced-field-zero.md)
- [The reduced field is its linear part plus the remainder](reduced-field-eq-mul-vec-add-remainder.md)
- [The first-order remainder of the reduced field at the trim](jacobian-remainder-reduced-field.md)
- [Sup-norm bounds on the remainder near the trim](longitudinal-remainder-bounds.md)
- [The reduced field is twice continuously differentiable](cont-diff-reduced-field.md)
- [Second derivatives of the reduced field](fderiv-fderiv-reduced-field-apply.md)
- [Bounds on the second derivatives of the reduced field on a box](norm-fderiv-fderiv-reduced-field-le.md)
- [Second-derivative bound on the remainder of the reduced field](jacobian-remainder-reduced-field-le-of-h.md)
- [Sup and Euclidean norms of a state](norm-of-lp-le-norm-le-two-mul.md)
- [The Euclidean ball of radius r lies in the box of radius r](abs-of-lp-le-of-norm-le.md)
- [Euclidean-norm bounds on the remainder near the trim](longitudinal-remainder-bounds-euclidean.md)
- [A planar plant solution moves forward at rate at least 99/100](planar-six-dof-plant-forward-rate.md)

## A Lyapunov certificate for the reduced linear plant

- [Lyapunov matrix of the reduced linear plant](longitudinal-lyapunov-matrix.md)
- [Reduced linear plant on the Euclidean state space](linear-reduced-field.md)
- [Quadratic Lyapunov function of the reduced plant](longitudinal-lyapunov.md)
- [The Lyapunov matrix is block diagonal](longitudinal-lyapunov-matrix-eq-from-blo.md)
- [The reduced linear plant is the derivative of the field at the trim](linear-reduced-field-eq-fderiv.md)
- [The Lyapunov matrix and the identity are positive definite](longitudinal-lyapunov-matrix-pos-def.md)
- [The Lyapunov matrix solves the Lyapunov equation with Q = 1](longitudinal-lyapunov-equation.md)
- [Quadratic comparison bounds for the Lyapunov function](longitudinal-lyapunov-bounds.md)
- [The Lyapunov function vanishes only at the trim](longitudinal-lyapunov-eq-zero-iff.md)
- [The Lyapunov function is differentiable](differentiable-longitudinal-lyapunov.md)
- [Derivative of the quadratic Lyapunov function](fderiv-longitudinal-lyapunov-apply.md)
- [Orbital derivative of the Lyapunov function along the linear plant](fderiv-longitudinal-lyapunov-linear-redu.md)
- [The reduced linear plant has a unique global solution](exists-unique-linear-reduced-field-solut.md)
- [Forward solutions of the linear plant decay exponentially](norm-le-of-is-integral-curve-on-linear-r.md)
- [The linear plant's initial-value problem has a decaying solution](linear-reduced-field-solution-decay.md)

## Local existence and decay of the nonlinear reduced flight

- [Nonlinear reduced field on the Euclidean state space](nonlinear-reduced-field.md)
- [Orbital derivative of the Lyapunov function along the nonlinear field](fderiv-longitudinal-lyapunov-nonlinear-r.md)
- [On the ball of radius 1/100 the orbital derivative is at most −V/4](fderiv-longitudinal-lyapunov-nonlinear-r-2.md)
- [In the ball the orbital derivative is negative exactly off the trim](fderiv-longitudinal-lyapunov-nonlinear-r-3.md)
- [A compact Lyapunov sublevel set between two balls](longitudinal-lyapunov-sublevel-spec.md)
- [Small Lyapunov sublevel sets are forward invariant](maps-to-sublevel-of-is-integral-curve-on.md)
- [Forward solutions that stay in the ball decay exponentially](norm-le-of-is-integral-curve-on-nonlinea.md)
- [Forward solutions starting near the trim decay exponentially](norm-le-of-is-integral-curve-on-nonlinea-2.md)
- [Forward solutions exist from states near the trim](exists-nonlinear-reduced-field-solution.md)
- [Near the trim a forward solution exists and decays exponentially](nonlinear-reduced-field-solution-decay.md)

- [Symmetric trim decouples longitudinal and lateral-directional dynamics](symmetric-trim-decouples-longitudinal-and-lateral-directional-dynamics.md)
