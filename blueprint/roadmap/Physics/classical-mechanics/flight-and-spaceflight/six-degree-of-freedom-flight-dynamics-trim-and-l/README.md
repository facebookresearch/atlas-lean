# Six-degree-of-freedom flight dynamics, trim and linearization

## A. Body velocity and the translational correspondence

- [Body Velocity](body-velocity.md)
- [Differentiable At body Velocity](differentiable-at-body-velocity.md)
- [Newton iff deriv body Velocity](newton-iff-deriv-body-velocity.md)

## B. The six-degree-of-freedom body equations

- [Six Dof Body Equations](six-dof-body-equations.md)
- [Balance Laws iff six Dof Body Equations](balance-laws-iff-six-dof-body-equations.md)

## C. Coefficient maps with admitted domains

- [Force Moment Maps](force-moment-maps.md)
- [Six Dof Plant](six-dof-plant.md)
- [Six Dof Plant iff](six-dof-plant-iff.md)

## D. A controlled longitudinal fixture

- [Lift Coeff](lift-coeff.md)
- [Drag Coeff](drag-coeff.md)
- [Flight Speed](flight-speed.md)
- [Lift Force](lift-force.md)
- [Drag Force](drag-force.md)
- [Aero Force](aero-force.md)
- [Actuator Force](actuator-force.md)
- [Pitch Moment](pitch-moment.md)
- [Reduced Field](reduced-field.md)
- [Actuator Box](actuator-box.md)
- [Pitch Orientation](pitch-orientation.md)
- [Longitudinal Maps](longitudinal-maps.md)
- [Planar Motion](planar-motion.md)
- [Planar State](planar-state.md)
- [Drag Coeff eq](drag-coeff-eq.md)
- [Lift and drag](lift-force-drag-force-spec.md)
- [The force balance](aero-force-add-actuator-force-add-weight.md)
- [Restriction of the plant to the plane](planar-six-dof-plant-iff.md)
- [The trim is a relative equilibrium](trim-relative-equilibrium.md)
- [Actuator domain](actuator-box-bounds.md)
- [No evaluation outside the box](longitudinal-maps-rejects.md)

## E. Linearization about the trim

- [Longitudinal Jacobian](longitudinal-jacobian.md)
- [Longitudinal Remainder](longitudinal-remainder.md)
- [Longitudinal Jacobian eq from Blocks](longitudinal-jacobian-eq-from-blocks.md)
- [The Jacobian at the trim](has-fderiv-at-reduced-field-zero.md)
- [Linear part and remainder](reduced-field-eq-mul-vec-add-remainder.md)
- [The first-order remainder at the trim](jacobian-remainder-reduced-field.md)
- [Remainder bounds, sup norm](longitudinal-remainder-bounds.md)
- [Cont Diff reduced Field](cont-diff-reduced-field.md)
- [The actual second derivatives](fderiv-fderiv-reduced-field-apply.md)
- [Hessian bounds on the box](norm-fderiv-fderiv-reduced-field-le.md)
- [The component-Hessian remainder theorem, instantiated](jacobian-remainder-reduced-field-le-of-h.md)
- [Sup and Euclidean norms of a state](norm-of-lp-le-norm-le-two-mul.md)
- [The Euclidean ball lies in the box](abs-of-lp-le-of-norm-le.md)
- [Remainder bounds, Euclidean norm](longitudinal-remainder-bounds-euclidean.md)
- [No stationary world position](planar-six-dof-plant-forward-rate.md)

## F. A Lyapunov certificate for the reduced linear plant

- [Longitudinal Lyapunov Matrix](longitudinal-lyapunov-matrix.md)
- [Linear Reduced Field](linear-reduced-field.md)
- [Longitudinal Lyapunov](longitudinal-lyapunov.md)
- [Longitudinal Lyapunov Matrix eq from Blocks](longitudinal-lyapunov-matrix-eq-from-blo.md)
- [The linearization](linear-reduced-field-eq-fderiv.md)
- [Definiteness of the certificate](longitudinal-lyapunov-matrix-pos-def.md)
- [The Lyapunov equation](longitudinal-lyapunov-equation.md)
- [Comparison bounds](longitudinal-lyapunov-bounds.md)
- [The trim is the only zero of `V`](longitudinal-lyapunov-eq-zero-iff.md)
- [Differentiable longitudinal Lyapunov](differentiable-longitudinal-lyapunov.md)
- [The derivative of `V`](fderiv-longitudinal-lyapunov-apply.md)
- [The orbital derivative along the plant](fderiv-longitudinal-lyapunov-linear-redu.md)
- [The actual global solution](exists-unique-linear-reduced-field-solut.md)
- [Exponential decay, by the direct method](norm-le-of-is-integral-curve-on-linear-r.md)
- [Decay of the actual initial-value problem](linear-reduced-field-solution-decay.md)

## G. Local existence and decay of the nonlinear reduced flight

- [Nonlinear Reduced Field](nonlinear-reduced-field.md)
- [The explicit field](of-lp-nonlinear-reduced-field.md)
- [The orbital derivative](fderiv-longitudinal-lyapunov-nonlinear-r.md)
- [The Lyapunov inequality on the ball](fderiv-longitudinal-lyapunov-nonlinear-r-2.md)
- [Strict decay only away from the trim](fderiv-longitudinal-lyapunov-nonlinear-r-3.md)
- [The invariant sublevel set](longitudinal-lyapunov-sublevel-spec.md)
- [Sublevel invariance](maps-to-sublevel-of-is-integral-curve-on.md)
- [Conditional decay from the Lyapunov inequality](norm-le-of-is-integral-curve-on-nonlinea.md)
- [Local exponential decay](norm-le-of-is-integral-curve-on-nonlinea-2.md)
- [Existence by compact-exit continuation](exists-nonlinear-reduced-field-solution.md)
- [Local existence and decay](nonlinear-reduced-field-solution-decay.md)
