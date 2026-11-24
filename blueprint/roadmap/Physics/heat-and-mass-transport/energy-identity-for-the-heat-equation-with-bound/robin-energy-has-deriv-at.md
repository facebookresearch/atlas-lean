# Robin conditions give the energy identity a quadratic boundary term

Let `k > 0` and let `D`, `L`, `h₀`, `h_L`, `Ta` and `t` be real; let `u` and `ux` be functions of
time and position, and write `θ(x) = u(t, x) - Ta`. Assume the outward Robin conditions
`k ux(t, 0) = h₀ θ(0)` and `-k ux(t, L) = h_L θ(L)`, and that `E(τ) = ∫_0^L (u(τ, x) - Ta)²/2 dx`
has at `t` the derivative given by the [energy identity](heat-energy-has-deriv-at.md) with no
source:

`-D ∫_0^L ux(t, x)² dx + D (θ(L) ux(t, L) - θ(0) ux(t, 0))`.

Then `E` has at `t` the derivative

`-D ∫_0^L ux(t, x)² dx - (D/k) (h₀ θ(0)² + h_L θ(L)²)`.
