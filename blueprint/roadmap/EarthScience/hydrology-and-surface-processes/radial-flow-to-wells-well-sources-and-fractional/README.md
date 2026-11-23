# Radial flow to wells, well sources and fractional flow

## Radial Darcy head profile

- [Logarithmic radial Darcy head profile](radial-darcy-head.md)
- [Radial Darcy head difference on an annulus around a well](radial-darcy-head-sub.md)
- [The logarithmic head profile carries the prescribed discharge](radial-darcy-head-solves.md)

## Matching the Thiem profile

- [The Thiem rate is minus the outward discharge](thiem-profile-outward-discharge.md)
- [The radial Darcy head difference is the Thiem one at the reversed rate](radial-darcy-head-sub-eq-thiem.md)

## Rejected inputs

- [No head finite at the axis carries a nonzero radial discharge](radial-darcy-no-head-at-axis.md)
- [A negative transmissivity sends the discharge up the head gradient](radial-discharge-upgradient-of-neg.md)

## Cells with wells

- [Cell rate of a finite-volume chain with wells](well-cell-rate.md)
- [Enthalpy flux through a face](face-enthalpy-flux.md)
- [Well energy rate of a cell](well-energy-rate.md)
- [Finite-volume ledger with wells](stock-add-mul-well-cell-rate.md)

## Mass and energy ledgers

- [Production enthalpy from the stored cell state](well-energy-rate-eq-stored.md)
- [Mass and energy ledgers with well and boundary sources](well-boundary-ledger.md)

## Fractional flow

- [Water fractional flow with quadratic relative permeabilities](frac-flow.md)
- [Fractional-flow derivative formula](frac-flow-deriv.md)
- [Bound on the fractional-flow derivative](frac-flow-bound.md)
- [End values of the fractional flow](frac-flow-zero-one.md)
- [The fractional flow is differentiable for positive viscosities](has-deriv-at-frac-flow.md)
- [Fractional-flow slope is nonnegative and bounded on the unit interval](frac-flow-deriv-mem-icc.md)
- [Lipschitz bound for the fractional flow on the unit interval](frac-flow-sub-mem-icc.md)
- [The fractional flow is nondecreasing on the unit interval](monotone-on-frac-flow.md)

## Normalized saturation and the CFL number

- [Normalized water saturation](norm-sat.md)
- [CFL number of the normalized upwind update](cfl-number.md)
- [Normalized saturation in the unit interval exactly on the mobile range](norm-sat-mem-icc-iff.md)

## The upwind step: monotonicity, interval and balance

- [Local upwind update of a cell](upwind-update.md)
- [Normalized upwind step on a chain with inflow](upwind-step.md)
- [Physical upwind step of the water saturations](sat-step.md)
- [The upwind update is monotone under the CFL condition](upwind-update-mono.md)
- [The upwind step keeps normalized saturations in the unit interval](upwind-step-mem-icc.md)
- [The physical saturation step normalizes to the upwind step](norm-sat-sat-step.md)
- [The saturation step keeps saturations in the mobile range](sat-step-mem-icc.md)
- [The upwind step in conservative finite-volume form](upwind-step-eq-discrete-balance.md)
- [Inlet-minus-outlet balance of the normalized saturations](sum-upwind-step.md)
- [Inlet-minus-outlet water volume balance](sat-step-volume-balance.md)
