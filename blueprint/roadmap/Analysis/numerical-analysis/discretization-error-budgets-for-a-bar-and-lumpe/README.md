# Discretization error budgets for a bar and lumped cooling

## Amplitude, unit profile and the physical reconstruction

- [Amplitude of the uniformly loaded fixed-fixed bar](bar-amplitude.md)
- [Unit bar profile](unit-profile.md)
- [Unit interpolation error](unit-error.md)
- [Physical P1 reconstruction of the bar displacement](physical-p1.md)
- [Physical error of the P1 bar reconstruction](physical-error.md)
- [Unit profile solves the unit bar problem](unit-profile-is-classical-solution.md)
- [Bar displacement is the amplitude times the unit profile](axial-displacement-eq-bar-amplitude-mul.md)
- [P1 bar reconstruction is the scaled Galerkin solution](physical-p1-eq-galerkin.md)
- [Pulled-back unit profile solves the fixed-fixed bar problem](is-fixed-fixed-solution-bar-amplitude-mu.md)
- [Dirichlet values of the P1 bar reconstruction](physical-p1-zero-and-length.md)

## Inverse normalization and the zero load

- [Bar amplitude vanishes exactly for zero load](bar-amplitude-ne-zero-iff.md)
- [Unit profile recovered from the bar displacement](unit-profile-eq-inv-bar-amplitude-mul.md)
- [Inverse amplitude map fails at zero load](zero-load-inverse-ne.md)
- [Zero load of the fixed-fixed bar](zero-load.md)

## Scaling of the two error integrals

- [Physical bar error is the amplitude times the unit error](physical-error-eq.md)
- [Energy of the physical bar error](integral-energy-physical-error.md)
- [Squared L² norm of the physical bar error](integral-sq-physical-error.md)

## The mesh estimates in physical form

- [Mesh bound on the squared L² norm of the physical bar error](integral-sq-physical-error-le-mesh.md)
- [Energy error of the P1 bar reconstruction](integral-energy-physical-error-le-mesh.md)

## Two uniform cells

- [Two-cell uniform partition of the unit interval](two-cells.md)
- [Unit interpolation error on two cells](unit-error-two-cells.md)
- [Physical bar error on two cells](physical-error-two-cells.md)

## The bath-cooling trajectory and the one-node storage law

- [Power delivered by a thermal bath](bath-power.md)
- [Thermal time constant](thermal-time-constant.md)
- [Bath-cooling trajectory](bath-trajectory.md)
- [Explicit Euler step for bath cooling](bath-euler-step.md)
- [Bath-cooling trajectory solves the bath equation](bath-trajectory-solves.md)
- [Stored heat of the bath-cooling trajectory](bath-trajectory-storage.md)
- [Single thermal node without a source keeps its temperature](one-node-no-source-const.md)

## Ten Euler steps of size `τ / 10`

- [Ten-step Euler error for bath cooling is nonzero](bath-euler-ten-step-error-pos.md)
- [Euler recurrence for bath cooling at step $\tau/10$](bath-euler-closed-form.md)
- [Ten Euler steps of bath cooling are within $|\Delta|/10$](bath-euler-ten-step-error.md)

## Time units and the unstable step

- [Bath Euler step is invariant under a common time unit](bath-euler-step-time-unit.md)
- [Mismatched time units in the bath Euler step](bath-euler-step-minutes-seconds.md)
- [Euler step of three time constants is unstable for bath cooling](bath-euler-three-tau.md)

## Classical Runge–Kutta steps on the bath-cooling model

- [Bath-cooling vector field](bath-field.md)
- [RK4 step on the bath field does not depend on the start time](bath-field-rk4-time-indep.md)
- [RK4 step on the bath field is a shifted linear-decay step](bath-field-rk4-shift.md)
- [One-stage Runge–Kutta step on the bath field is the Euler step](bath-field-euler-step.md)
- [RK4 step on the bath field via the stability polynomial](bath-field-rk4-step.md)

## Ten Runge–Kutta steps of size `τ / 10`

- [Excess after ten RK4 steps of bath cooling](bath-rk4-ten-step-excess.md)
- [Ten-step RK4 error bound for bath cooling](bath-rk4-ten-step-error.md)
- [Ten-step RK4 error for bath cooling is nonzero](bath-rk4-ten-step-error-pos.md)
- [RK4 recurrence for bath cooling at step $\tau/10$](bath-rk4-closed-form.md)

## The unstable Runge–Kutta step

- [RK4 step of three time constants is unstable for bath cooling](bath-rk4-three-tau.md)

## Defects through the Euler recurrence

- [Residual of a computed sequence in the bath Euler recurrence](bath-euler-residual.md)
- [Bath Euler step of a tenth of the time constant contracts differences by 9/10](bath-euler-step-sub-tenth.md)
- [Defect recurrence for a computed bath-cooling sequence](defect-recurrence.md)
- [Ten-step error budget scales with the temperature unit](ten-step-error-budget-temp-unit.md)
- [Ten-step Euler error budget](ten-step-error-budget.md)
- [Three-term error budget for ten computed Euler steps](bath-euler-total-error.md)
