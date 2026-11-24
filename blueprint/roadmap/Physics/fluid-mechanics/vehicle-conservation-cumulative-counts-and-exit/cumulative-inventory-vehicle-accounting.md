# Cell-chain total: initial count plus boundary inflow minus outflow

Let `k(j, i)` and `F(j, i)` be real numbers indexed by the time step `j` and the cell or face `i`
(natural numbers), and let `dt ≥ 0` and `dx > 0`. If the densities follow the conservative update
`k(j + 1, i) = k(j, i) + (dt / dx) (F(j, i) - F(j, i + 1))` for all `j` and `i`, then for every
number of cells `n` and of steps `m` the total vehicle count of the cells `0, …, n - 1` satisfies

`∑_{i < n} dx k(m, i) = ∑_{i < n} dx k(0, i) + ∑_{j < m} dt F(j, 0) - ∑_{j < m} dt F(j, n)`:

the initial total plus the cumulative inflow through the first face minus the cumulative outflow
through the last face `n`; the interior face fluxes cancel.
