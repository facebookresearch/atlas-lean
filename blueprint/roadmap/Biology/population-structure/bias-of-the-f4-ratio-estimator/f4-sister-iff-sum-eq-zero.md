# Graph criterion for the f4-ratio sister condition

In every [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights `w` and
drift lengths `ℓ`, and for all populations `A, O, Y, B, C`, the f4 equality
`f4(A, O; Y, C) = f4(A, O; B, C)` assumed by
[f4-ratio estimation](../patterson-s-f-statistics/f4-ratio.md) holds if and only if
`∑ e, (w A e - w O e) * (w Y e - w B e) * ℓ e = 0`, where `f4` is the
[f4 statistic](../patterson-s-f-statistics/f4.md) of the
[population frequencies](../patterson-s-f-statistics/freq.md). Equivalently,
[`f4(A, O; Y, B) = 0`](f4-sister-iff-f4-eq-zero.md).
