# For $b \ge 0$ and a rate-one exponential clock $r_1$, the event $b r_1 < 0$ has probability zero

Let `r₁, r₂` be independent exponential clocks with rate `1`, with joint law `Exp(1) ⊗ Exp(1)` on
`ℝ²` (each factor with [density](exp-dens.md) `exp(-x)` for `x ≥ 0` and `0` for `x < 0`). For
every real `b ≥ 0`, the event `b r₁ < 0 · r₂`, that is `b r₁ < 0`, has probability `0`. It is the
event `b r₁ < a r₂` that channel `1` rings first (as in the [holding time](hold.md)) when
channel `1` has speed `a = 0`: a channel of speed `0` almost surely does not ring first.
