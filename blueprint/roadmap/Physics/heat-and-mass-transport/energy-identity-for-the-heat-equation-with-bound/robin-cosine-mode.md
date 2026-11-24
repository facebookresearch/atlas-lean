# A decaying cosine mode satisfies Robin conditions with h = kμ tan μL/2

Let `k > 0`, `μ ≥ 0`, `L ≥ 0` with `μL/2 < π/2`, and let `D` and `Ta` be real. Let

`u(t, x) = Ta + e^{-Dμ²t} cos(μ(x - L/2))` and `h = kμ tan(μL/2)`.

Then, at every `(t, x)`, `u` has the time derivative `ut = -Dμ² e^{-Dμ²t} cos(μ(x - L/2))`, the
spatial derivative `ux = -μ e^{-Dμ²t} sin(μ(x - L/2))` and the second spatial derivative
`uxx = -μ² e^{-Dμ²t} cos(μ(x - L/2))`, and `ut = D uxx`. For every `t` the outward Robin conditions
`k ux(t, 0) = h (u(t, 0) - Ta)` and `-k ux(t, L) = h (u(t, L) - Ta)` hold, `h ≥ 0`, and
`u(t, 0) - Ta ≠ 0`: the mode is a nonzero example.
