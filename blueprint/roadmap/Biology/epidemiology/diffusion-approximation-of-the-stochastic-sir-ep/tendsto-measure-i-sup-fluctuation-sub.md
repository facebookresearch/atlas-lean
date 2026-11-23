# Diffusion approximation, supremum form

Under the hypotheses of
`tendsto_measure_fluctuation_sub`, the supremum over `[0, T]` of
`‖√N (X_N(t) - x(t)) - U(t)‖` is at least `ε` with probability tending to `0`:

`P(sup_{t ∈ [0, T]} ‖√N (X_N(t) - x(t)) - U(t)‖ ≥ ε) → 0`  as `N → ∞`.

The supremum is taken in `ℝ≥0∞`, so it exists for every path, bounded or not, and need not be
attained. The event lies inside the event of `tendsto_measure_fluctuation_sub` at threshold
`ε / 2`; it is not assumed measurable, and `μ` is applied as an outer measure.
