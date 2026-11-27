# Infinite-sites mutation on the Kingman genealogy

For a natural number `n` and `θ ≥ 0`, the Kingman mutation kernel sends real epoch lengths
`t = (t_k)_{2 ≤ k ≤ n}` to the law of independent Poisson counts `N_b` on the
[branches](kingman-branch.md) `b = (k, j)` of the Kingman genealogy, with means

`(θ / 2) ℓ_b(t) = (θ / 2) max(t_k, 0)`,

the [branch-mutation kernel](branch-mutation-kernel.md) with rate `θ / 2` and the
[branch lengths](kingman-branch-length.md) `ℓ_b`, which truncate the epoch lengths at `0`: the
mean is `0` when `t_k ≤ 0`. It is infinite-sites mutation at rate `θ / 2` per lineage per unit
time, with `θ = 4Nu` and time in units of `2N` generations.
