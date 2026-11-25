# Displacement gradient

For a displacement field `u : ℝ³ → ℝ³` and a point `x ∈ ℝ³`, the displacement gradient at `x` is the
`3 × 3` matrix `H` with entries `H_ij = d/dt u_i(x + t e_j)` at `t = 0`, where `e_j` is the `j`-th
coordinate vector: row `i` is the component of `u`, column `j` the direction. So `H_ij` is the
partial derivative `∂u_i/∂x_j (x)` when it exists; with the convention that the derivative is `0`
where it does not exist, the entry is `0` otherwise. For `u` differentiable at `x`, `H` is its
Jacobian matrix.
