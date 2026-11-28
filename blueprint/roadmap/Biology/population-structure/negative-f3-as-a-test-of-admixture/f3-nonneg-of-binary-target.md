# Binary targets have nonnegative f3 for unit-interval source weights

In a [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights `w`, let
`C, A, B` be populations such that every weight `w C e` of the target is `0` or `1` and the source
weights lie in `[0, 1]`: `0 ≤ w A e ≤ 1` and `0 ≤ w B e ≤ 1` for every edge `e`. Then
`f3(C; A, B) ≥ 0` for the [f3 statistic](../patterson-s-f-statistics/f3.md) of the
[population frequencies](../patterson-s-f-statistics/freq.md). The sources need not have binary
weights, so `A` and `B` may themselves be admixed.
