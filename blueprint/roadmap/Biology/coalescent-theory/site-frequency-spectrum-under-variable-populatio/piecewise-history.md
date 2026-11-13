# Piecewise-constant population-size history

A **piecewise-constant population-size history with `K` pieces**: piece `j < K` starts at
time `start j` (backward from the present, `start 0 = 0`, strictly increasing) and has
relative size `size j > 0`; the last piece extends to infinity. Adjacent pieces may have equal
sizes, so this also covers histories with fewer than `K` distinct pieces. Values at indices
`j ≥ K` are unused. The case `K = 0` is degenerate (its size function is `0`); the theorems
about `c_m` assume `0 < K` where it matters.
