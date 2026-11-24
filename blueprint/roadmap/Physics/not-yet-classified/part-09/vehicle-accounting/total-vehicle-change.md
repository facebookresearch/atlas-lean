# Total vehicle change

Vehicle accounting over a finite cell chain. Cells `0, ..., n-1`
have densities `k i` and face fluxes `F i` between cell `i - 1` and
cell `i` (with `F 0` the external inflow and `F n` the external
outflow). Under the conservative update
`k' i = k i + (dt / dx) * (F i - F (i + 1))`, the total vehicle
count changes by exactly `dt * (F 0 - F n)`: every internal face is
counted once as an outflow and once as an inflow, so only the two
external faces survive the telescoping sum.
