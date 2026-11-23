# Directional derivative of a GNSS pseudorange

Let `x₀ ≠ s` be points of three-dimensional Euclidean space (receiver and satellite positions),
`d` a direction, `b₀` a clock bias and `db` a clock-bias rate. The pseudorange along the line
through `(x₀, b₀)`, `r(t) = ‖x₀ + t d - s‖ + (b₀ + t db)`, has derivative
`⟪x₀ - s, d⟫ / ‖x₀ - s‖ + db` at `t = 0`, where `⟪·, ·⟫` is the Euclidean inner product: the
Jacobian row `[(x₀ - s) / ‖x₀ - s‖, 1]` dotted with `(d, db)`.
