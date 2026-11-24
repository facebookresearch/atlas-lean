# Expected pairwise differences of one pair in the marked Kingman model

For `n ≥ 2`, `θ ≥ 0` and every [pair](../segregating-sites-and-pairwise-differences/sample-pairs.md)
`s` of genes of a sample of size `n`, under the
[marked Kingman model](kingman-tree-mutation-measure.md) the
[number of differences](pair-diff.md) `D_s = ∑_{b ∈ P_h(s)} N_b` of the pair, computed from the
history coordinate `h` and the mutation counts `N`, has mean

`E[D_s] = θ`.

Indeed its [conditional mean](cond-exp-pair-diff-of-mutation.md) given the genealogy is `θ τ_s`,
where the [coalescence time](pair-coal-time.md) `τ_s` of the pair has
[mean one](integral-pair-coal-time-kingman-genealog.md).
