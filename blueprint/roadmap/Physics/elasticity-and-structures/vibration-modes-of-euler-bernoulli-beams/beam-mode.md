# Simply supported beam mode

For a positive integer `k` and reals `L` (beam length), `ω` (angular frequency), `x` and `t`,
`w(x, t) = sin(kπx / L) cos(ω t)`, the `k`-th simply supported mode with unit amplitude. It
[vanishes at `x = 0`](beam-mode-zero-left.md) and, for `L ≠ 0`,
[at `x = L`](beam-mode-zero-right.md); for `EI, ρA > 0` and `L ≠ 0` it
[solves the beam equation](beam-mode-beam-equation.md) `ρA w_tt + EI w_xxxx = 0` at the
[modal frequency](beam-freq.md) `ω = ω_k`. With the convention `x / 0 = 0`, `w = 0` everywhere when
`L = 0`. In the physical reading `L > 0`.
