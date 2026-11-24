# Energy of the simply supported mode

For reals `EI`, `ρA`, `L` and `ω`, a positive integer `k` and a time `t`,
`E(t) = ∫₀ᴸ (ρA (∂w / ∂t)² + EI (∂²w / ∂x²)²) / 2 dx`, the kinetic plus bending energy of the
[simply supported mode](beam-mode.md) `w(x, t) = sin(kπx / L) cos(ω t)` (an oriented integral, so
the sign changes for `L < 0`). The derivatives are classical, since `w` is smooth in `x` and `t` for
every `L`. For `L = 0` the integral is over a single point and `E(t) = 0` (the mode itself is `0`
then, by the convention `x / 0 = 0`). In the physical reading `L > 0`, `EI > 0` and `ρA > 0`; the
definition allows all real values.
