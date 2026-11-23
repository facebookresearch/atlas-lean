# Grubbs' G statistic

Grubbs' statistic `G = max_i |x i - x̄| / s` of a sample: the largest absolute deviation from
the sample mean over the [sample standard deviation](sample-std-dev.md), and `0` when `s = 0` (no
spread, hence no rejection). The maximum is over the whole sample
([every standardized residual is at most G](div-le-grubbs-g.md)) and, for `s ≠ 0`, is
[attained by an observation](exists-grubbs-g-eq.md). Grubbs' procedure needs at least three
observations (its [rejection rule](grubbs-reject.md) requires it); for two distinct observations
`G = 1/√2` whatever the data. Tabulated critical values assume i.i.d. normal sampling.
