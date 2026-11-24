# When the f4 ratio equals the admixture proportion

In a [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights `w`, let
`A, O, X, Y, B, C` be populations and `α` a real number with `w X e = α * w Y e + (1 - α) * w C e`
for every edge `e`, and suppose `f4(A, O; B, C) ≠ 0`, where `f4` is the
[f4 statistic](../patterson-s-f-statistics/f4.md) of the
[population frequencies](../patterson-s-f-statistics/freq.md). Then
`f4(A, O; X, C) / f4(A, O; B, C) = α` if and only if `α = 0` or `f4(A, O; Y, C) = f4(A, O; B, C)`,
the f4 equality assumed by [f4-ratio estimation](../patterson-s-f-statistics/f4-ratio.md). The
criterion is an equality between two statistics, not a condition on the topology of a graph.
