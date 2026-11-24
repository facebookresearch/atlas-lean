# Merging a pair of positions is merging two blocks

For a list `b` of block sizes and natural numbers `i < j`, [merging the blocks](merge-set.md) at
the positions `{i, j}` gives the same list as
[merging two blocks](../../expected-site-frequency-spectrum/merge-blocks.md) of `b` at `i` and
`j`. The only hypothesis is `i < j`. If `j` is a position of `b`, both remove the blocks at `i`
and `j` and append a block of their total size. If only `i` is a position of `b`, both delete the
entry at `i` and append its value. If neither is, both append a block of size `0` to `b`.
