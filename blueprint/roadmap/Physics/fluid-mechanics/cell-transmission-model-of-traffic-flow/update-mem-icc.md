# Under the CFL condition one update keeps the density between 0 and kj

Let `v`, `w` and `kj` be positive, let the densities of a cell and of its upstream and downstream
neighbours satisfy `0 ≤ k ≤ kj`, `0 ≤ k_in ≤ kj` and `0 ≤ k_out ≤ kj`, and let the time step
`dt ≥ 0` and the cell length `dx > 0` satisfy the CFL condition `(dt / dx) max(v, w) ≤ 1`. Then the
updated density

`k + (dt / dx) (F(k_in, k) - F(k, k_out))`

lies between `0` and `kj`, where `F(k_up, k_down)` is the [face flux](face-flux.md)
`min(D(k_up), S(k_down))`: one cell-transmission step preserves the admissible densities.
