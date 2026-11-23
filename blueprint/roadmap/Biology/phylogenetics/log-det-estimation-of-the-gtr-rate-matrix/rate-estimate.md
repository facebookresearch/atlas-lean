# Rate Estimate

The **log-det rate estimate**: the log-det generator divided by the log-det distance. Its
trace is `-1` when every base-frequency estimate is positive and the log-det distance is nonzero
(`trace_rateEstimate`); when `logDetDistance F = 0`, Lean's `0⁻¹ = 0` makes it the zero
matrix.
