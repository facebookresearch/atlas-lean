# Pivot Interval

The interval `[t - hi * s, t - lo * s]` for a realized statistic `t`, a scale `s` and an
acceptance region `[lo, hi]` (MF06.4). For `0 < s`, the hypothesis of the lemmas below, it is the
set of parameter values `θ` whose pivot `(t - θ) / s` lies in `[lo, hi]`
(`mem_pivotInterval_iff`). It is computed from data and carries no coverage claim; a coverage
probability follows only from a hypothesis on the law of the pivot
(`measure_mem_pivotInterval`). Mathlib has no confidence-interval definition.
