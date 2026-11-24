# The upwind update conserves the total for every Courant number

For real values `c_i` on `n ≥ 1` periodic cells indexed by `ℤ/nℤ` and every real `ν`, the
first-order upwind update `c⁺_i = (1 - ν) c_i + ν c_{i-1}`, where `i - 1` is taken modulo `n`,
conserves the total: `∑_i c⁺_i = ∑_i c_i`, because the periodic shift `i ↦ i - 1` permutes the
cells.
