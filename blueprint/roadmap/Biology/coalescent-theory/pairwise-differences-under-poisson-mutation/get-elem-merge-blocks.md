# Entries of the list after merging two blocks

Let `B₀, …, B_{r-1}` be blocks of sampled genes and `x < y < r`. After
[merging the blocks](../ranked-labeled-histories-of-coalescent-trees/merge-blocks.md) at positions `x` and
`y`, which leaves `r - 1` blocks, the block at position `j < r - 1` is `B_x ∪ B_y` if `j = x`,
`B_j` if `j < y` and `j ≠ x`, and `B_{j+1}` if `j ≥ y`.
