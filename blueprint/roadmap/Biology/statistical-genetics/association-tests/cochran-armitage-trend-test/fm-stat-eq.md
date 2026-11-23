# The fixed-margin statistic as a normalized contrast

For `R ≤ N` and any centring `μ` and
scale `v > 0`, with `B = √(R (N - R) N v)`,
`fmStat R N g = (U / B)² / ((N ∑ x² - (∑ x)²) / (N² v))`, where `x k = score (g k)` and
`U = ∑_{k < N} fmWeight R N k · (x k - μ)` is the trend numerator. Degenerate designs
(`R = 0` or `R = N`) and tables with zero score variance give `0` on both sides.
