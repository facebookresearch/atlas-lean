# X ji mul x ij of one add mul eq zero

For `[Field F]`, `i ≠ j`, `a b : F` with `1 + a * b = 0`, we have
`x j i b * x i j a = x i j (-a) * weyl i j (Units.mk0 a ha)` where `ha : a ≠ 0`
is derived from `h`. Derives `a ≠ 0` from field nontriviality, `b = -a⁻¹`,
builds the unit from `a`, and applies `x_ji_neg_inv_mul_x_ij`. Preserves factor
order and signs; characteristic-two safe.
