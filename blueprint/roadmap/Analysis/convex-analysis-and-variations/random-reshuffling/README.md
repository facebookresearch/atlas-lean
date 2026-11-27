# Random reshuffling

Random reshuffling takes component gradient steps in a freshly sampled,
uniform order in each epoch. The reference prefix uses that same order but
freezes the component gradients at a minimizer of the finite-sum objective.

The labels visited in a prefix of length $k$ form a uniform $k$-subset:
every such subset is the prefix set of exactly $k!(N-k)!$ permutations of
the $N$ labels. The sampling identities below apply to this prefix even
when distinct labels have the same vector value.

- [Random reshuffling epoch iteration](reshuffling-epoch-iteration.md)
- [Random reshuffling reference prefix at a minimizer](reference-prefix-at-minimizer.md)
- [Mean of a vector sample without replacement](vector-sample-mean-without-replacement.md)
- [Mean-square error of a vector sample mean without replacement](vector-sample-mean-square-error-without-replacement.md)
