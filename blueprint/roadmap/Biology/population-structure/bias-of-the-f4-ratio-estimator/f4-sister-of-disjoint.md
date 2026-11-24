# No edge separating both pairs gives the f4-ratio sister condition

In a [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights `w`, let
`A, O, Y, B, C` be populations such that every edge `e` with `w Y e ≠ w B e` (separating `Y` from
`B`) has `w A e = w O e` (a zero `A`–`O` weight contrast; on a tree, the edge lies off the
`A`–`O` path), that is
`(w A e - w O e) * (w Y e - w B e) = 0` for every edge `e`. Then `f4(A, O; Y, C) = f4(A, O; B, C)`
for the [f4 statistic](../patterson-s-f-statistics/f4.md) of the
[population frequencies](../patterson-s-f-statistics/freq.md). The condition is sufficient, not
necessary: by the [graph criterion](f4-sister-iff-sum-eq-zero.md) the equality only needs the
weighted sum over the edges to vanish, which can also happen through cancellation between edges.
