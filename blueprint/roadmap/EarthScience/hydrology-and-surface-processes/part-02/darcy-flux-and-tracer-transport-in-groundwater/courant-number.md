# Courant number of the pore velocity

For a Darcy discharge `q`, a porosity `n`, a time step `dt` and a cell width `dx` (real numbers),
the Courant number of the pore velocity `q / n` is `|q / n| * dt / dx`. It is only this
dimensionless expression; no stability of a numerical scheme is asserted. It is defined for all
real inputs, with the convention `x / 0 = 0`: it is `0` when `n = 0` or `dx = 0`. The intended
domain is `0 < n ≤ 1`, `dt ≥ 0` and `dx > 0`.
