# Conservative shared-face step in mass form

For a natural number `n`, real numbers `A` (cross-section), `Δx` (cell length) and `Δt` (time step),
face fluxes `F`, and cell values `c` and `c'` indexed by `ℤ/nℤ` (for `n = 0` this is `ℤ`), the step
from `c` to `c'` is conservative when `A Δx c'(i) = A Δx c(i) + Δt (F(i) - F(i + 1))` for every cell
`i`: the mass of cell `i` gains the inflow through its left face `i` and loses the outflow through
its right face `i + 1`.
