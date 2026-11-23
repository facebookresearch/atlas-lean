# Trace normalization of the rate estimate

If every base-frequency estimate is positive
and the log-det distance is nonzero, `rateEstimate F` has trace `-1`. Without the second
hypothesis the claim fails: at `logDetDistance F = 0` the estimate is the zero matrix
(Lean's `0⁻¹ = 0`).
