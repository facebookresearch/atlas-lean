# Position of a block after two blocks merge

For natural numbers `x`, `y` and `p`, the new position of the block at position `p` when the
blocks at positions `x` and `y` are merged: it is `x` if `p = y`, `p - 1` if `p > y`, and `p` if
`p < y`. The formula is defined for all `x`, `y` and `p`, and is meant for `x < y`:
[merging the blocks](../ranked-labeled-histories-of-coalescent-trees/merge-blocks.md) at positions `x < y`
puts their union at position `x` and removes position `y`, so the blocks above `y` move down by
one place and the others keep their positions.
