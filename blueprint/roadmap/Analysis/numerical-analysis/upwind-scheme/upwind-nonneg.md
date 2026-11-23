# The upwind update preserves nonnegativity under the CFL condition

Let `c_i ≥ 0` be values on `n ≥ 1` periodic cells indexed by `ℤ/nℤ`, and let `ν` satisfy the CFL
condition `0 ≤ ν ≤ 1`. Then every cell of the first-order upwind update
`c⁺_i = (1 - ν) c_i + ν c_{i-1}`, where `i - 1` (taken modulo `n`) is the upstream neighbour, is
nonnegative.
