# Reduced acceleration of the two-link pendulum by Cramer's rule

For real `m₁`, `m₂`, `l₁`, `l₂`, `g` and vectors `q`, `w` of the Euclidean plane, let `f = (f₁, f₂)`
be the [generalized force](generalized-force.md) at `(q, w)`, `c = cos (q₁ - q₂)` and
`D = l₁² l₂² m₂ (m₁ + m₂ sin² (q₁ - q₂))` the [determinant](mass-matrix-det.md) of the reduced mass
matrix. The reduced acceleration is

`((m₂ l₂² f₁ - m₂ l₁ l₂ c f₂) / D, ((m₁ + m₂) l₁² f₂ - m₂ l₁ l₂ c f₁) / D)`.

For positive masses and lengths `D > 0` and this is `M(q)⁻¹ f(q, w)`
([inverse form](reduced-accel-eq-inv-mul-vec.md)). With the convention `x / 0 = 0`, both components
are `0` where `D = 0`, for example when `m₂ = 0` or a length is `0`.
