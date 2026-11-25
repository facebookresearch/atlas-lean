# The pooled variance is unbiased under the equal-variance model

Let `X i`, `i : Fin m`,
and `Y j`, `j : Fin n`, with `m, n ≥ 2`, be two samples on a probability space. Each sample is
pairwise independent and identically distributed (common laws those of `X i0` and `Y j0`) with
finite second moment, and the two variances are equal: `Var Y j0 = Var X i0`, the
equal-variance model hypothesis. Then the pooled variance of the two samples is integrable and
its expectation is the common variance. No normality and no independence between the two samples
are needed: each sample variance is unbiased, and the pooled variance is
[their weighted average](pooled-variance-eq-weighted.md).
