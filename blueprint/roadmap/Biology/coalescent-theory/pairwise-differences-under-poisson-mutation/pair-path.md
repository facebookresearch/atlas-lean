# Branches separating two sampled genes

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes and `s` a set of sampled genes. The branches separating the genes of `s` are the
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the genealogy with exactly
one gene of `s` [below them](branch-block.md). For a pair `s = {a, b}` of distinct genes these
are the branches ancestral to exactly one of `a` and `b`; they form the path between the two
genes through their most recent common ancestor (MRCA). For the empty set there are none, and for
a single gene `a` they are all the branches ancestral to `a`, one per epoch, so for `n ≥ 2` this
set is not empty, unlike the path from a gene to itself.
