# Cumulative inventory vehicle Accounting

Cumulative inventory for the total vehicle count of a
finite cell chain. If densities `k j i` evolve by the
conservative update
`k (j + 1) i = k j i + dt / dx * (F j i - F j (i + 1))` with
face fluxes `F j`, then after `nSteps` steps the total count
`∑ i, dx * k nSteps i` is the initial total plus cumulative
boundary arrivals `∑ j, dt * F j 0` minus cumulative boundary
departures `∑ j, dt * F j nCells`. The per-step total change
is the vehicle-accounting identity.
