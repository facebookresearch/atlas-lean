# Merging shortens a block list by one if the removed position exists

For a list `B_0, …, B_{r-1}` of `r` blocks of sampled genes, any natural number `x` and a
position `y < r`,
[merging the blocks at positions `x` and `y`](../ranked-labeled-histories-of-coalescent-trees/merge-blocks.md)
gives a list of `r - 1` blocks: the merge writes `B_x ∪ B_y` at position `x` and then removes the
entry at position `y`. Only `y < r` is required. For `x < r` and `x ≠ y` this merges the two
blocks into one. For `x ≥ r` nothing is written, and for `x = y` the written block is the one
removed, so in these two cases the list just loses `B_y`.
