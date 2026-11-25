# Mean overlap of the paths of two disjoint pairs

Let `a`, `b`, `c`, `d` be four distinct genes of a sample of size `n`. In the
[Kingman genealogy](kingman-genealogy-measure.md) of the sample (independent epoch lengths, the
epoch with `k` lineages exponential with rate `C(k, 2) = k (k - 1) / 2`, and an independent
ranked labeled history drawn by random joining), the [total length](pair-path-overlap.md)
`ℓ(P_{ab} ∩ P_{cd})` of the branches that separate both `{a, b}` and `{c, d}` has mean

`E[ℓ(P_{ab} ∩ P_{cd})] = 2/3`.

At the start the four genes are in four distinct lineages, from which the
[remaining overlap](sum-mul-apart4-future-overlap.md) of the two paths has mean `2/3`.
