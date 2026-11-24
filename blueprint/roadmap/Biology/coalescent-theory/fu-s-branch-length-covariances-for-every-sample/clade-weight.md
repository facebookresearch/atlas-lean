# Clade weight of $m$ of $k$ lineages

For natural numbers `k` and `m`, the clade weight is `w_k(m) = 2 / (m C(k, m))` if `1 ≤ m < k`, and
`w_k(m) = 0` otherwise; on `1 ≤ m < k` the denominator is positive. It is the expected total time
during which a given set of `m` of `k` lineages of Kingman's coalescent forms exactly one block,
over the levels from `k` lineages down to `2` (level `k` included), when the holding time while `l`
lineages remain has mean `1 / C(l, 2)`.
