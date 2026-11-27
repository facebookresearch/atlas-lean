# Cumulative link inventory

Cumulative vehicle inventory from per-step link balance.
If the vehicle count `N` evolves by
`N (j + 1) = N j + dt * (Fin j - Fout j)` at every step (the
finite-cell balance with boundary in/out fluxes), then after
`n` steps the count is the initial count plus cumulative
arrivals `∑ j < n, dt * Fin j` minus cumulative departures
`∑ j < n, dt * Fout j`, with both count origins explicit. No
FIFO or delay conclusion is asserted from aggregate
conservation.
