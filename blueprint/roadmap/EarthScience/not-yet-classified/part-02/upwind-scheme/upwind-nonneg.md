# Upwind nonneg

Periodic first-order upwind update preserves nonnegativity under the
CFL condition `0 ≤ ν ≤ 1`: with `c⁺ i = (1 - ν) * c i + ν * c (i - 1)` on
`ZMod n` (periodic cells, `i - 1` the upstream neighbour), every updated
cell is nonnegative when every `c i` is.
