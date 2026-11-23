# Kurtz's theorem for SIR, supremum form

Under the hypotheses of
`tendsto_measure_deviation`, the supremum over `[0, T]` of the deviation between the scaled chain
and the ODE solution is at least `ε` with probability tending to `0`:

`P(sup_{t ∈ [0, T]} |S/N - s| + |I/N - i| + |R/N - r| ≥ ε) → 0`  as `N → ∞`.

The supremum is taken in `ℝ≥0∞` (the deviation is nonnegative), so it exists for every path,
bounded or not, and need not be attained. The event lies inside the event of
`tendsto_measure_deviation` at threshold `ε / 2`; it is not assumed measurable, and `μ` is applied
as an outer measure.
