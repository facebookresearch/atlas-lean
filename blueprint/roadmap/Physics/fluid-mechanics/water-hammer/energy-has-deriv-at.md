# Energy balance of the water-hammer equations

Let `a`, `g`, `A` and `L` be positive (wave speed, gravitational acceleration, pipe area, pipe
length), and let `h`, `q` (head and discharge) and `h_t`, `h_x`, `q_t`, `q_x` be real functions of
`(t, x)`. Suppose that, for every time `t` and every `x ∈ [0, L]`, `h(·, x)` and `q(·, x)` have the
derivatives `h_t(t, x)` and `q_t(t, x)` at `t`, `h(t, ·)` and `q(t, ·)` have the derivatives
`h_x(t, x)` and `q_x(t, x)` at `x` within `[0, L]`, the water-hammer equations
`h_t + (a² / (g A)) q_x = 0` and `q_t + g A h_x = 0` hold, and `h_t` and `q_t` are continuous on
`ℝ × [0, L]`.

Then the energy `E(t) = ∫_0^L ((g A / a²) h(t, x)² / 2 + q(t, x)² / (2 g A)) dx` has, at every time
`t`, the derivative `E'(t) = h(t, 0) q(t, 0) - h(t, L) q(t, L)`: the head-discharge flux in at
`x = 0` minus the flux out at `x = L`. The physical energy is `ρ g` times `E`; that factor is not
part of the identity.
