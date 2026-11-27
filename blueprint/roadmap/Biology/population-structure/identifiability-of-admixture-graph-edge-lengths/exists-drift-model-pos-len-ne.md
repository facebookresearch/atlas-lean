# Positive edge lengths are not identifiable when edges outnumber pairs

Let `P` be a finite set of `n` populations and `E` a finite set of edges, with more edges than pairs
of distinct populations, `n choose 2 = n (n - 1) / 2 < |E|`. For every
[drift model](../patterson-s-f-statistics/drift-model.md) with populations `P` and edges `E`, on any
measure space, whose drift lengths are all positive, `ℓ(e) > 0`, there is a drift model on the
counting measure of `E` (each edge a point, every subset measurable) with the same lineage weights,
with all drift lengths positive but a different drift-length vector, and with the same value of the
[f4 statistic](../patterson-s-f-statistics/f4.md) `f4(A, B; C, D)` of its population frequencies for
all populations `A, B, C, D`. Hence it also has the same [f2](../patterson-s-f-statistics/f2.md) and
[f3](../patterson-s-f-statistics/f3.md) statistics, which are values of f4:
`f2(A, B) = f4(A, B; A, B)` and `f3(C; A, B) = f4(C, A; C, B)`.
