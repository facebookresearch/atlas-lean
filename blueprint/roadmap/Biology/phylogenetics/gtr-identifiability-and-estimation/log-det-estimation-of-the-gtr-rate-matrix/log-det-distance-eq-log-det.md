# Paralinear form of the log-det distance

Let `ι` be a finite set of states. Let `F` be a real `ι × ι` matrix whose
[base-frequency estimates](base-freq.md) `b(F) i = (∑_j F i j + ∑_j F j i) / 2` are all positive and
whose [normalized divergence matrix](norm-divergence.md) `N(F)` is positive definite. Then the
[log-det distance](log-det-distance.md) `Δ(F)` is the
[LogDet (paralinear) distance](../../pulley-principle-logdet-distances-and-felsenstei/paralinear.md) of
the symmetrized divergence matrix `F_s = (F + Fᵀ) / 2`, both of whose marginals are `b(F)`:
`Δ(F) = -log (det F_s) + ∑_i log (b(F) i)` (Lake 1994; Lockhart, Steel, Hendy and Penny 1994).
