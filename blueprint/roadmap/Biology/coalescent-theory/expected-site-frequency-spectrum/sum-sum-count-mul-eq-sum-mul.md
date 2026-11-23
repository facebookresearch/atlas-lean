# Sum sum count mul eq sum mul

Pathwise decomposition of the total branch length over frequency classes,
in the unfolded form of `sfsLength` and `KingmanTimes.totalLength`: if for every
`k ∈ [2, n]` the block-size list `ps.getD (n - k) []` has `k` positive entries
summing to `n` (as every list visited by random joining from `n` singletons
does), then for all holding times `T`,
`∑_{i=1}^{n-1} ∑_{k=2}^{n} #{blocks of size i among k} · T k = ∑_{k=2}^{n} k · T k`,
i.e. `∑_i L_i = L`.
