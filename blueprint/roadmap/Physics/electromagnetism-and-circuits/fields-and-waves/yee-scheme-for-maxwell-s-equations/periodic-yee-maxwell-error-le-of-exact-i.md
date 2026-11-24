# With exact staggered initial data the Yee error bound has no mismatch

Under the hypotheses of the [error bound](periodic-yee-maxwell-error-le.md) (a periodic grid of
`N > 0` cells of width `h > 0`, `L = N h`, `dt > 0`, the Courant bound `c dt / h ≤ ρ < 1`, and
`E_y`, `H_z` periodic, separately three times continuously differentiable, with third-derivative
bounds, whose polarized fields satisfy the vacuum Maxwell equations at `c`), start from the exact
samples `E0 = (E_y(0, j h))_j` and `H0 = (H_z(−dt/2, j h − h/2))_j`. Then for every step `n` with
`n dt ≤ T`, the [normalized error](normalized-field-error.md) is at most
`√((1 + ρ) / (1 − ρ)) · T √L (Mt dt² + c Mx h²) / 6`, with `Mt` and `Mx` the
[time](energy-time-bound.md) and [space](energy-space-bound.md) bounds in energy coordinates.
