# For $a \ge 0$ and a rate-one exponential clock $r_2$, the event $a r_2 < 0$ has probability zero

Let `r₁, r₂` be independent exponential clocks with rate `1`, with joint law `Exp(1) ⊗ Exp(1)` on
`ℝ²` (each factor with [density](exp-dens.md) `exp(-x)` for `x ≥ 0` and `0` for `x < 0`). For
every real `a ≥ 0`, the event `a r₂ < 0 · r₁`, that is `a r₂ < 0`, has probability `0`. It is the
event `a r₂ < b r₁` that channel `2` rings first (as in the [holding time](hold.md)) when
channel `2` has speed `b = 0`: a channel of speed `0` almost surely does not ring first.
