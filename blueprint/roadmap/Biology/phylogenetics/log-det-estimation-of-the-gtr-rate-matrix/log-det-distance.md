# Log-det distance

Let `ι` be a finite set of states. For a real `ι × ι` matrix `F` with
[normalized divergence matrix](norm-divergence.md) `N(F)`, the log-det distance is
`Δ(F) = -tr (log N(F)) = -∑_k log λ_k`, where `λ_k` are the eigenvalues of the symmetric matrix
`N(F)`, counted with multiplicity, with the conventions `log 0 = 0` and `log x = log |x|` for
`x < 0`. When `N(F)` is positive definite it is `-log det N(F)`
([log-determinant form](log-det-distance-eq-neg-log-det.md)); if moreover every base-frequency
estimate is positive, it is the
[LogDet (paralinear) distance](../pulley-principle-logdet-distances-and-felsenstei/paralinear.md) of
the symmetrized divergence matrix ([paralinear form](log-det-distance-eq-log-det.md)).
