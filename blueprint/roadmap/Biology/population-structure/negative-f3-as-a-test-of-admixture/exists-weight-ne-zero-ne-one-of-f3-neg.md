# Negative f3 forces a nonbinary target for unit-interval source weights

In a [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights `w`, let
`C, A, B` be populations whose sources have weights in `[0, 1]`: `0 ≤ w A e ≤ 1` and `0 ≤ w B e ≤ 1`
for every edge `e`. If `f3(C; A, B) < 0` for the [f3 statistic](../patterson-s-f-statistics/f3.md)
of the [population frequencies](../patterson-s-f-statistics/freq.md), then some edge `e` has
`w C e ≠ 0` and `w C e ≠ 1`: the target `C` does not have the binary weights of an unadmixed
population. No range is assumed on the weights of `C`. This is the contrapositive of the
[nonnegative f3 of a binary target](f3-nonneg-of-binary-target.md); on an admixture graph the
condition on the sources always holds ([graph form](exists-weight-ne-zero-ne-one-of-f3-neg-2.md)).
