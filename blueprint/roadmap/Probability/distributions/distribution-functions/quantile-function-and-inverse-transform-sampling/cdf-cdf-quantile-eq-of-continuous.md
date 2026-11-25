# Quantile inversion under a continuous cdf

Assume `u ∈ Set.Ioo (0 : ℝ) 1`.

When `cdf μ` is continuous, the cdf at the
generalized inverse quantile is exactly `u`. (`cdfQuantile_mem` gives `≥`; continuity rules out
`>`, since just below the quantile the cdf is `< u`.)
