# For D ≥ 0, L, k > 0, h ≥ 0 the Robin problem has at most one solution

Let `D ≥ 0`, `L > 0`, `k > 0`, `h₀ ≥ 0`, `h_L ≥ 0` and `Ta`, `T` be real. Let `u₁`, `u₂`, `ux₁`,
`ux₂` be functions of time and position, and write `w = u₁ - u₂` and `wx = ux₁ - ux₂`. Assume:

- for every `t` with `0 < t < T`, both fields satisfy the outward Robin conditions
  `k uxᵢ(t, 0) = h₀ (uᵢ(t, 0) - Ta)` and `-k uxᵢ(t, L) = h_L (uᵢ(t, L) - Ta)`;
- for every `t` with `0 < t < T`, the difference energy `E(τ) = ∫_0^L w(τ, x)²/2 dx` has at `t` the
  derivative `-D ∫_0^L wx(t, x)² dx + D (w(t, L) wx(t, L) - w(t, 0) wx(t, 0))`, the
  [energy identity](heat-energy-has-deriv-at.md) with no source;
- `E` is continuous on `[0, T]`, and `w(t, ·)` is continuous on `[0, L]` for every `t` in `[0, T]`;
- `u₁(0, x) = u₂(0, x)` for `0 ≤ x ≤ L`.

Then `u₁(t, x) = u₂(t, x)` for all `t` in `[0, T]` and `x` in `[0, L]`.
