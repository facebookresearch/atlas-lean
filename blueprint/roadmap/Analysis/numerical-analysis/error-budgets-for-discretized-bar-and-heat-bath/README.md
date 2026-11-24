# Error budgets for discretized bar and heat-bath models

## The bar: amplitude, unit profile and reconstruction

- [Amplitude of a fixed-fixed bar under uniform load](bar-amplitude.md)
- [Unit displacement profile of a fixed-fixed bar](unit-profile.md)
- [Interpolation error of the unit profile](unit-error.md)
- [Piecewise linear reconstruction of the bar displacement](physical-p1.md)
- [Error of the reconstructed bar displacement](physical-error.md)
- [The unit profile solves −û″ = 2 with zero end values](unit-profile-is-classical-solution.md)
- [The bar displacement is the amplitude times the rescaled unit profile](axial-displacement-eq-bar-amplitude-mul.md)
- [The reconstruction vanishes at both ends of the bar](physical-p1-zero-and-length.md)
- [The reconstruction is the amplitude times the unit Galerkin solution](physical-p1-eq-galerkin.md)

## Inverse normalisation and the zero load

- [With nonzero rigidity and length the amplitude is zero only for q = 0](bar-amplitude-ne-zero-iff.md)
- [For nonzero amplitude the unit profile is recovered from the bar](unit-profile-eq-inv-bar-amplitude-mul.md)
- [At zero load the displacement, reconstruction and error vanish](zero-load.md)
- [At zero load the inverse amplitude map does not recover the profile](zero-load-inverse-ne.md)

## Scaling and mesh bounds of the bar error

- [The bar error is the amplitude times the rescaled unit error](physical-error-eq.md)
- [Energy of the bar error in terms of the unit error](integral-energy-physical-error.md)
- [Squared L² norm of the bar error in terms of the unit error](integral-sq-physical-error.md)
- [Mesh bound on the energy of the bar error](integral-energy-physical-error-le-mesh.md)
- [Mesh bound on the squared L² norm of the bar error](integral-sq-physical-error-le-mesh.md)

## Two equal cells

- [Partition of the unit interval into two equal cells](two-cells.md)
- [Unit interpolation error on two equal cells](unit-error-two-cells.md)
- [Bar error on two equal cells](physical-error-two-cells.md)

## The bath-cooling model

- [Heat delivered by a bath at fixed temperature](bath-power.md)
- [Thermal time constant of a body coupled to a bath](thermal-time-constant.md)
- [Temperature of a body cooling in a bath](bath-trajectory.md)
- [Explicit Euler step for a body in a bath](bath-euler-step.md)
- [The bath-cooling trajectory solves C T′ = Q(T)](bath-trajectory-solves.md)
- [The stored heat of the cooling body changes at the bath power](bath-trajectory-storage.md)
- [Without a source a lumped body keeps its temperature](one-node-no-source-const.md)

## Ten Euler steps of size τ/10

- [Euler steps of size τ/10 multiply the excess by 9/10 each](bath-euler-closed-form.md)
- [Ten Euler steps of size τ/10 are within a tenth of the excess](bath-euler-ten-step-error.md)
- [The ten-step Euler error is positive for a nonzero excess](bath-euler-ten-step-error-pos.md)

## Time units and the unstable Euler step

- [A common change of time unit leaves the Euler step unchanged](bath-euler-step-time-unit.md)
- [A step sixty times too large multiplies the excess by −5](bath-euler-step-minutes-seconds.md)
- [Euler steps of size 3τ double the excess with alternating sign](bath-euler-three-tau.md)

## Runge–Kutta steps on the bath model

- [Right-hand side of the bath-cooling equation](bath-field.md)
- [The one-stage Runge–Kutta step of the bath field is the Euler step](bath-field-euler-step.md)
- [A Runge–Kutta step of the bath field does not depend on the time](bath-field-rk4-time-indep.md)
- [A Runge–Kutta step of the bath field acts on the excess temperature](bath-field-rk4-shift.md)
- [A Runge–Kutta step of the bath field multiplies the excess by R(z)](bath-field-rk4-step.md)
- [Runge–Kutta steps of size τ/10 multiply the excess by 72387/80000](bath-rk4-closed-form.md)
- [Excess temperature after ten Runge–Kutta steps of size τ/10](bath-rk4-ten-step-excess.md)
- [The ten-step Runge–Kutta error is below 10⁻⁶ of a nonzero excess](bath-rk4-ten-step-error.md)
- [The ten-step Runge–Kutta error is positive for a nonzero excess](bath-rk4-ten-step-error-pos.md)
- [Runge–Kutta steps of size 3τ multiply the excess by 11/8](bath-rk4-three-tau.md)

## Residuals and the ten-step error budget

- [Residual of a computed temperature sequence in the Euler recurrence](bath-euler-residual.md)
- [Ten-step error budget of a computed temperature sequence](ten-step-error-budget.md)
- [An Euler step of size τ/10 scales temperature differences by 9/10](bath-euler-step-sub-tenth.md)
- [The defect of a computed sequence obeys a damped recurrence](defect-recurrence.md)
- [A computed temperature after ten steps lies within its error budget](bath-euler-total-error.md)
- [A change of temperature unit scales the residuals and the budget](ten-step-error-budget-temp-unit.md)

## The two-cell bar system

- [Stiffness of the interior node of the two-cell bar](two-cell-stiffness.md)
- [Consistent load of the interior node of the two-cell bar](two-cell-load.md)
- [Interior coefficient of the two-cell reconstruction](two-cell-coeff.md)
- [Residual of an approximate interior coefficient](two-cell-residual.md)
- [Reconstruction from an interior coefficient through the hat function](two-cell-reconstruction.md)
- [Unit stiffness and load at the interior node of two cells](two-cells-interior-system.md)
- [The interior stiffness is the unit stiffness scaled by EA/L](two-cell-stiffness-eq-stiffness.md)
- [The interior stiffness is the energy of the rescaled hat](integral-energy-hat.md)
- [The consistent load is the load integrated against the rescaled hat](integral-load-hat.md)
- [The two-cell reconstruction is the hat times its midpoint value](physical-p1-eq-two-cell-reconstruction.md)
- [Closed form of the interior coefficient](two-cell-coeff-eq.md)
- [The interior coefficient solves the one-equation system K c = F](two-cell-stiffness-mul-two-cell-coeff.md)

## Residual and reconstruction error of the two-cell bar

- [The coefficient error is the residual divided by the stiffness](two-cell-coeff-sub-eq.md)
- [The residual bounds the coefficient error](abs-two-cell-coeff-sub-le.md)
- [Every hat reconstruction vanishes at both ends of the bar](two-cell-reconstruction-zero-and-length.md)
- [The reconstruction error is the coefficient error times the hat](physical-p1-sub-two-cell-reconstruction.md)
- [On the bar the reconstruction error is bounded by the residual](abs-physical-p1-sub-two-cell-reconstruct.md)
- [Energy of the reconstruction error from the residual](integral-energy-reconstruction-error.md)
- [Squared L² norm of the reconstruction error](integral-sq-reconstruction-error.md)

## The quadratic load and midpoint quadrature

- [Unit profile for a quadratic load](quad-profile.md)
- [Composite midpoint rule for the load vector](midpoint-load.md)
- [The quadratic-load profile solves −û″ = ξ² with zero end values](quad-profile-is-classical-solution.md)
- [Exact interior load of the quadratic load on two cells](load-quad-two-cells.md)
- [Midpoint interior load of the quadratic load on two cells](midpoint-load-quad-two-cells.md)
- [Load and coefficient defects of the midpoint rule on two cells](quad-defects-two-cells.md)
- [Amplitude of a bar under a quadratic load](quad-amplitude.md)
- [Displacement of a bar under a quadratic load](quad-displacement.md)
- [Exact consistent load of the quadratic load at the interior node](quad-load.md)
- [Midpoint rule for the interior load on the bar](phys-midpoint-load.md)
- [The quadratic-load amplitude is twice the uniform-load amplitude](quad-amplitude-eq-two-mul.md)
- [The quadratic-load displacement solves the fixed-fixed bar problem](is-fixed-fixed-solution-quad-displacemen.md)
- [With nonzero rigidity and length β is zero only for Q = 0](quad-amplitude-ne-zero-iff.md)
- [For nonzero amplitude the quadratic-load profile is recovered](quad-profile-eq-inv-quad-amplitude-mul.md)
- [At zero quadratic load the displacement and both loads vanish](quad-zero-load.md)
- [The bar loads are Q L times the unit loads](quad-physical-loads.md)

## Coefficients and the composed error bounds

- [Exact-load interior coefficient for the quadratic load](quad-coeff.md)
- [Midpoint interior coefficient for the quadratic load](quad-midpoint-coeff.md)
- [Residual of an approximate coefficient in the midpoint system](quad-midpoint-residual.md)
- [The exact-load coefficient is 7β/192, the midpoint displacement](quad-coeff-eq.md)
- [The midpoint coefficient is 5β/128](quad-midpoint-coeff-eq.md)
- [The midpoint and exact-load coefficients differ by β/384](quad-midpoint-coeff-sub-quad-coeff.md)
- [Energy of the reconstructed quadrature error](integral-energy-quadrature-error.md)
- [Squared L² norm of the reconstructed quadrature error](integral-sq-quadrature-error.md)
- [The midpoint coefficient error is the residual over the stiffness](quad-midpoint-coeff-sub-eq.md)
- [Energy-norm error of an approximate midpoint coefficient](sqrt-energy-quad-error-le.md)
- [L² error of an approximate midpoint coefficient](sqrt-sq-quad-error-le.md)
- [Nodal exactness leaves the quadrature and off-node errors](nodal-exactness-not-enough.md)
