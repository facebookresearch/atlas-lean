# Mean overlap of the paths of two pairs sharing a gene

Let `a`, `b`, `c` be three distinct genes of a sample of size `n`. In the
[Kingman genealogy](kingman-genealogy-measure.md) of the sample (independent epoch lengths, the
epoch with `k` lineages exponential with rate `C(k, 2) = k (k - 1) / 2`, and an independent
ranked labeled history drawn by random joining), the [total length](pair-path-overlap.md)
`ℓ(P_{ab} ∩ P_{ac})` of the branches that separate both `{a, b}` and `{a, c}` has mean

`E[ℓ(P_{ab} ∩ P_{ac})] = 1`.

The overlap is the part of the tree from `a` up to the point where the paths to `b` and `c`
part; almost surely its length is `τ_{ab} + τ_{ac} - τ_{bc}`, and each
[coalescence time](pair-coal-time.md) has mean `1`.
