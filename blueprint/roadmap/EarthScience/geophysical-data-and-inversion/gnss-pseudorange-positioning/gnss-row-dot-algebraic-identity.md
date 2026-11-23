# Gnss row dot algebraic identity

Purely algebraic row-dot identity, for all `x₀` and `s`: the row
`[‖x₀ - s‖⁻¹ • (x₀ - s), 1]` dotted with `(d, db)` is `⟪x₀ - s, d⟫_ℝ / ‖x₀ - s‖ + db`.

It asserts no Jacobian or derivative. Only for `x₀ ≠ s` is this row the pseudorange Jacobian
row, by `gnss_directional_derivative`. At `x₀ = s` both sides equal `db` because `‖0‖⁻¹ = 0`,
while the range term `‖t • d‖ = |t| * ‖d‖` is not differentiable at `0` for `d ≠ 0`.
