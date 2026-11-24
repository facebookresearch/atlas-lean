# Upwind face flux on a periodic grid

For a natural number `n`, real numbers `A` (cross-section) and `v` (speed), cell values `c` indexed
by `ℤ/nℤ` (for `n = 0` this is `ℤ`) and a face `i`, the upwind face flux through face `i`, the face
between cell `i - 1` and cell `i`, counted positive toward increasing index, is
`A (max(v, 0) c(i - 1) + min(v, 0) c(i))`: the advective flux `v c` taken on the upstream side.
