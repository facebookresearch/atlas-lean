# For D > 0 the Dirichlet problem has at most one solution

Let `a < b`, `D > 0` and `T` be real, and let `c₁`, `c₂`, `w`, `wx`, `wxx`, `wt` be functions of
`(x, t)` such that:

- `w = c₁ - c₂` on the closed rectangle `[a, b] × [0, T]`, and `w` is continuous there;
- `wx`, `wxx` and `wt` are continuous on `[a, b] × (0, T)`, and at every point of
  `(a, b) × (0, T)` they are the derivatives `∂w/∂x`, `∂wx/∂x` and `∂w/∂t`, with `wt = D wxx`;
- `w(a, t) = w(b, t) = 0` for `0 < t < T`, and `w(x, 0) = 0` for `a ≤ x ≤ b`.

Then `c₁ = c₂` on `[a, b] × [0, T]`. The proof is the energy method: the
[energy](continuous-on-energy.md) `E(t) = ∫_a^b w(x, t)² dx` is continuous on `[0, T]` and, by the
[energy identity](energy-identity-deriv.md), has the derivative `-2D ∫_a^b wx(x, t)² dx ≤ 0` on
`(0, T)`. Nothing is assumed outside the rectangle, so `c₁` and `c₂` may be solutions that exist
only up to time `T`.
