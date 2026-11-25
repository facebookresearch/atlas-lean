# One shared branch per epoch once a pair has coalesced, none before

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `a` and `b` genes and `k` an epoch, `2 ≤ k ≤ n`. The number of
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of epoch `k` with both `a`
and `b` [below them](branch-block.md) is `0` if the pair `{a, b}` is [apart](pair-apart.md)
after the first `n - k` coalescence events and `1` otherwise. The genes need not be distinct:
for `a = b` the pair is never apart and the count is `1`. For distinct genes, the shared branch
of an epoch after their coalescence is the lineage ancestral to both; these branches run from
their most recent common ancestor (MRCA) up to the root.
