# Kink bundle for perfect-complements utility

For coefficients `a`, `b`, prices `p = (p₀, p₁)` and wealth `w`, the kink bundle is `(t / a, t / b)`
with `t = w / (p₀ / a + p₁ / b)`. It is defined for all real `a`, `b`, `p` and `w`: under the
convention `x / 0 = 0`, `x₀ = 0` when `a = 0`, `x₁ = 0` when `b = 0`, and the bundle is `(0, 0)`
when `p₀ / a + p₁ / b = 0`; the intended domain is `a, b > 0` with positive prices. When `a ≠ 0` and
`b ≠ 0` it lies on the ray `a x₀ = b x₁`, and when `p₀ / a + p₁ / b ≠ 0` its cost `p₀ x₀ + p₁ x₁` is
exactly `w`.
