# Lipschitz error propagation

If `f` is Lipschitz with constant `L`
(`LipschitzWith L f`, so `L : ℝ≥0` per Mathlib), then
`‖f (x + δ) - f x‖ ≤ L * ‖δ‖`. This is Mathlib's `LipschitzWith.dist_le_mul_of_le` read
with `dist_eq_norm` and `(x + δ) - x = δ`.
