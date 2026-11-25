# Coalescence time is a measurable function of the genealogy

For every natural number `n` and every set `s` of genes of a sample of size `n`, the
[coalescence time](pair-coal-time.md) `τ_s(t, h)` is a measurable function of the genealogy
`(t, h)`, made of real epoch lengths `t = (t_2, …, t_n)` and a
[ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h`
of the `n` genes, for the Borel σ-algebra on the epoch lengths and the σ-algebra of all sets of
histories. Here `τ_s(t, h)` is the sum of the `t_k`, `2 ≤ k ≤ n`, over the epochs `k` during
which `s` is [apart](pair-apart.md) in `h`, that is, no lineage after the first `n - k`
coalescence events contains all of `s`; for a pair, the epochs during which its two genes are in
different lineages.
