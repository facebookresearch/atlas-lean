# The separating path has length twice the apart epochs' positive parts

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `s` a [pair](../segregating-sites-and-pairwise-differences/sample-pairs.md) of two distinct sampled
genes and `t_k`, for `k = 2, …, n`, real epoch lengths, and give each branch of epoch `k` the
[length](../poisson-mutation-on-the-kingman-genealogy/kingman-branch-length.md) `max(t_k, 0)`. Then the
total length of the [branches separating the two genes](pair-path.md) is
`2 ∑_k max(t_k, 0)`, the sum running over the epochs `k` during which the genes of `s` are
[apart](pair-apart.md), that is, apart after the first `n - k` coalescence events. For
nonnegative epoch lengths this is twice the [coalescence time](pair-coal-time.md) of the pair;
a negative epoch length during which the pair is apart counts as `0` here but enters the
coalescence time as given.
