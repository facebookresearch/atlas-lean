# Branches shared by two sampled genes

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes and `s` a set of sampled genes. The branches shared by the genes of `s` are the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the genealogy with every
gene of `s` [below them](branch-block.md). For a pair `s = {a, b}` of distinct genes these are
the branches ancestral to both genes, above their most recent common ancestor (MRCA); under
infinite sites, a mutation on such a branch is carried by both genes and does not separate them.
For the empty set every branch qualifies, and for a single gene `a` they are the branches
ancestral to `a`, the same as the [branches with exactly one gene](pair-path.md) of `{a}` below
them.
