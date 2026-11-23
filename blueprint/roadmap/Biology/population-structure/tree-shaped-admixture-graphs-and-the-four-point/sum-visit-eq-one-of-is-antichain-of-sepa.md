# Cut lemma for lineage visit probabilities

Let `parents X` be the (finite, possibly more than two) parents of node `X`, with well-founded
parent relation, and let `prop X Y` be admixture proportions summing to `1` over the parents of
every non-root node. Let `visit X c` satisfy the first-step equation of the probability that the
lineage of `X`, traced toward the root, passes through `c`:
`visit X c = 1` if `X = c`, else `∑ Y ∈ parents X, prop X Y * visit Y c`.

If `S` is an antichain for the ancestor relation (no element of `S` is a proper ancestor of
another) and `S` separates `X` from `root` (every root-ward parent chain from `X` to `root` meets
`S`), then the visit probabilities of `X` across the cut sum to `1`.
