# Path of a continuous-time Markov chain

The **path** of the chain started at `i`: `X t = Y n` for the `n` with
`T n ≤ t < T (n + 1)`. If `t` is at or after the explosion time `sup T n` (a null event, by
`IsRateMatrix.ae_tendsto_ctmcJumpTime`), the value is an arbitrary state that does not depend
on `i`, `Q` or `ω`.
