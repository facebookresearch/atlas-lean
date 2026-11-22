# Exact coverage of the two-sided t-interval

For an i.i.d. `N(μ, v)` sample `X` of size
`n ≥ 2` with `v ≠ 0` and `α ∈ (0, 1)`, let `t = cdfQuantile (t_{n-1}) (1 - α/2)` be the upper
`α/2` point of Student's t law on `n - 1` degrees of freedom. The t-interval built from the sample
mean and the sample standard deviation covers `μ` with probability exactly `1 - α`. This is
`ProbabilityTheory.one_sample_t_interval_coverage_eq` restated with `tInterval`, `sampleMean` and
`sampleStdDev`.
