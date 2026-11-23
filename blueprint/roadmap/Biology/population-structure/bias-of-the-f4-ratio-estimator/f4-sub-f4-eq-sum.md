# The f4 difference of the sister condition as an edge sum

In every [drift model](../patterson-s-f-statistics/drift-model.md) with lineage weights `w` and
drift lengths `ℓ`, and for all populations `A, O, Y, B, C`, the two sides of the f4 equality assumed
by [f4-ratio estimation](../patterson-s-f-statistics/f4-ratio.md) differ by the weighted overlap of
the `A`–`O` path with the `Y`–`B` difference:
`f4(A, O; Y, C) - f4(A, O; B, C) = ∑ e, (w A e - w O e) * (w Y e - w B e) * ℓ e`, where `f4` is the
[f4 statistic](../patterson-s-f-statistics/f4.md) of the
[population frequencies](../patterson-s-f-statistics/freq.md). The reference population `C` cancels.
