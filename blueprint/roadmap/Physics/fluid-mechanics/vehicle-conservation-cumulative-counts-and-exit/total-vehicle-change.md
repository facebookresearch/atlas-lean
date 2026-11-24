# Vehicle accounting over a finite chain of cells

Let `n` be a natural number, `k_i` the densities of the cells `0, …, n - 1`, `F_i` the face fluxes
(`F_i` between cells `i - 1` and `i`, `F_0` the external inflow and `F_n` the external outflow),
`dt` a time step and `dx > 0` a cell width. Under the conservative update
`k_i' = k_i + (dt / dx) (F_i - F_{i+1})`, the total vehicle count changes by
`∑_{i < n} dx (k_i' - k_i) = dt (F_0 - F_n)`: every internal face is counted once as an outflow and
once as an inflow, so only the two external faces remain.

Equivalently, the change is `dx dt` times the total discrete balance of the face fluxes, the inflow
minus the outflow per unit width summed over the cells:
`∑_{i < n} dx (k_i' - k_i) = dx dt ∑_{i < n} (F_i - F_{i+1}) / dx`.
