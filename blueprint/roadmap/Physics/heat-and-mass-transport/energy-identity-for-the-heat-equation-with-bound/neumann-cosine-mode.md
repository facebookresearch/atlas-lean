# For L > 0 the cosine mode cos(πx/L) has zero flux at both ends

Let `L > 0`, let `D`, `k` and `Ta` be real, and let `μ = π/L` and
`u(t, x) = Ta + e^{-Dμ²t} cos(μx)`. Then at every `(t, x)` the map `u(t, ·)` has the derivative
`ux(t, x) = -μ e^{-Dμ²t} sin(μx)`, and for every `t`

`k ux(t, 0) = 0 · (u(t, 0) - Ta)`, `-k ux(t, L) = 0 · (u(t, L) - Ta)` and `u(t, 0) - Ta ≠ 0`:

the Robin conditions with zero transfer coefficients, that is zero flux, hold at both ends with a
nonzero boundary excess. The time derivative and the heat equation are not part of this statement;
the [Robin cosine mode](robin-cosine-mode.md) carries them.
