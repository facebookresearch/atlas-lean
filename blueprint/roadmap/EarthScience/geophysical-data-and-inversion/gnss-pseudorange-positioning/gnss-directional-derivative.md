# Gnss directional derivative

GNSS pseudorange directional derivative: for receiver `x₀`, satellite `s`, `x₀ ≠ s`,
direction `d` and clock rate `db`, the pseudorange `r(t) = ‖x₀ + t • d - s‖ + (b₀ + t * db)`
has derivative at `0` equal to `⟪x₀ - s, d⟫_ℝ / ‖x₀ - s‖ + db`, i.e. the Jacobian row
`[(x₀ - s) / ‖x₀ - s‖, 1]` dotted with `(d, db)`.
