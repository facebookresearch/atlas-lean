# The joint maximum-likelihood estimate

For real pairs
`y i 0, y i 1`, `i < n`, with `∑_i (y_{i1} - y_{i2})² > 0`, the log-likelihood over pair means
`α ∈ ℝⁿ` and variance `s > 0` is maximized exactly at `α̂_i = (y_{i1} + y_{i2}) / 2` and
`s = σ̂² = (1 / (4n)) ∑_i (y_{i1} - y_{i2})²`: for every `α` and every `s > 0` the log-likelihood
is at most its value there, with equality only when `α = α̂` and `s = σ̂²`.

## Sources

- J. Neyman and E. L. Scott, "Consistent estimates based on partially consistent observations", Econometrica 16 (1948) 1–32; the characterization is derived.
