# Branch counts of the marked Kingman model are conditionally Poisson

For a natural number `n` and `θ ≥ 0`, under the [marked Kingman model](kingman-mutation-measure.md)
the branch counts `N` (the second coordinate) have conditional law the
[Kingman mutation kernel](kingman-mutation-kernel.md) given the epoch-length vector `t` of its
[holding times](of-mutation-model.md): given `t`, the counts are independent Poisson with means
`(θ / 2) max(t_k, 0)` on the `k` branches of epoch `k`.
