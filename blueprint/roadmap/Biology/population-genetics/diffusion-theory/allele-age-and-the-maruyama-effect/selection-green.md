# Sojourn density of the Wright–Fisher diffusion with selection

The sojourn density (Green's function) of the Wright–Fisher diffusion with genic selection,
time in units of `2N` generations, `σ = 2Ns`. With `u = kimuraFixation σ` and
`u'(x) = kimuraSlope σ · e^{-2σx}`,

`Ψ(p, x) = 2 u(min p x) (1 - u(max p x)) / (x (1 - x) u'(x))`,

which is `2 S(min p x) (S(1) - S(max p x)) / (S(1) x (1 - x) e^{-2σx})` in terms of the scale
function `S(y) = (1 - e^{-2σy}) / (2σ)` (`S(y) = y` if `σ = 0`). The neutral case is handled by
the neutral branches of `kimuraFixation` and `kimuraSlope` (`selectionGreen_zero`). It is
meaningful for `0 < x < 1`; at `x = 0, 1` the denominator vanishes and Lean's `/ 0` gives `0`
(a null set for integrals in `x`). In the diffusion reading (not formalized here), `Ψ(p, x) dx`
is the expected time an allele started at frequency `p` spends in `(x, x + dx)` before loss or
fixation (Ewens 2004, Chapter 4; the paper's `Ψ(p, x)` divided by `2N`).
