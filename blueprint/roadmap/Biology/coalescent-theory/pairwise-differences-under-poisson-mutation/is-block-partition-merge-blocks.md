# Merging two blocks of a block partition gives a block partition

Let `B₀, …, B_{r-1}` be a [block partition](is-block-partition.md) of the sample with positions
`pos`, and let `x < y < r`. Then the list obtained by
[merging the blocks](../ranked-labeled-histories-of-coalescent-trees/merge-blocks.md) at positions `x` and
`y` is a block partition with positions `a ↦ m(pos a)`, where `m(p) = x` if `p = y`,
`m(p) = p - 1` if `p > y` and `m(p) = p` if `p < y` (the [new position](merge-idx.md) of each
block).
