# Solute transport with linear sorption

Explicit time stepping of solute concentrations in a network of cells exchanging a fixed flow of
carrier water, with linear sorption to the solid phase and first-order loss. The step updates the
stored mass by arc transfers, sources and retirements, and keeps nonnegative concentrations
nonnegative when the time step satisfies a budget.

## Balance and the concentration step

- [Carrier-water balance of a cell network](is-carrier-balanced.md)
- [Explicit concentration step of solute transport in a cell network](concentration-step.md)

## Stored mass and total balance

- [The concentration step as a stored-mass update](concentration-step-inventory.md)
- [Total stored mass after a concentration step](concentration-step-total.md)

## Nonnegativity under a time-step budget

- [Nonnegativity of the concentration step](concentration-step-nonneg.md)
- [Nonnegative stored mass after a concentration step with linear sorption](stored-mass-concentration-step-nonneg.md)
