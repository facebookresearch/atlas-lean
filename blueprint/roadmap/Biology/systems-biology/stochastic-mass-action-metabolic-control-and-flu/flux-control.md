# Flux control coefficient

The flux control coefficient `C^{J_j}_{e_i} = (e_i / J_j) ∂J_j/∂e_i`. It is meaningful
when `J_j ≠ 0` and the steady-state flux is differentiable at `e`; otherwise Lean's `x / 0 = 0`
and `fderiv` of a non-differentiable map, `0`, give junk values.
