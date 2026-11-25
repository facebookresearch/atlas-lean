# Algebraic identity for the GNSS row dotted with a direction

For all points `x₀`, `s` and `d` of three-dimensional Euclidean space and every real `db`,
`⟪‖x₀ - s‖⁻¹ (x₀ - s), d⟫ + 1 · db = ⟪x₀ - s, d⟫ / ‖x₀ - s‖ + db`, where `⟪·, ·⟫` is the
Euclidean inner product: the row `[‖x₀ - s‖⁻¹ (x₀ - s), 1]` dotted with `(d, db)`.

The identity is algebraic and says nothing about derivatives. Only for `x₀ ≠ s` is this row the
[Jacobian row of the pseudorange](gnss-directional-derivative.md). At `x₀ = s` both sides equal
`db`, with the conventions `0⁻¹ = 0` and `0 / 0 = 0`, while the range term `‖t d‖ = |t| ‖d‖` is
not differentiable at `t = 0` for `d ≠ 0`.
