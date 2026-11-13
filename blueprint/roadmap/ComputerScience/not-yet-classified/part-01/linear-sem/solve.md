# Solve

The solution of the recursive linear structural equations `X = B X + e` on the nodes
`Fin n`: `X = (1 - B)⁻¹ e`. Here `B i j` is the coefficient of `X_j` in the equation of `X_i`
and `e` is the noise vector. For strictly lower triangular `B` this is the unique solution
(`eq_solve_iff`).
