# Energy identity with boundary work for the heat equation at one time

Let `0 ≤ L`, `D` and `t` be real, and let `u`, `ut`, `ux`, `uxx` and `src` be functions of time and
position. Assume that at time `t`, for every `x` with `0 ≤ x ≤ L`: `u(·, x)` has the derivative
`ut(t, x)` at `t`; `u(t, ·)` has the derivative `ux(t, x)` at `x`; `ux(t, ·)` has the derivative
`uxx(t, x)` at `x`; and `ut(t, x) = D uxx(t, x) + src(t, x)`. Assume also that `u(t, ·)`, `ux(t, ·)`
and `uxx(t, ·)` are continuous on `[0, L]`, that `x ↦ u(t, x) ut(t, x)` is integrable on `[0, L]`,
and that the energy `E(τ) = ∫_0^L u(τ, x)²/2 dx` has the derivative `∫_0^L u(t, x) ut(t, x) dx` at
`t` (differentiation under the integral). Then `E` has at `t` the derivative

`-D ∫_0^L ux(t, x)² dx + D (u(t, L) ux(t, L) - u(t, 0) ux(t, 0)) + ∫_0^L u(t, x) src(t, x) dx`.

The three terms are the diffusion contribution, the boundary work at the two ends, kept explicitly,
and the source power. The diffusion contribution is a dissipation when `D ≥ 0`. All hypotheses
concern the single time `t`.
