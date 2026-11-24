# Merging the blocks at a set of positions

For a list `b` of block sizes and a finite set `K` of positions (numbered from `0`), the merged
list removes the entries of `b` at the positions in `K`, keeps the order of the others, and
appends one block whose size is `∑_{m ∈ K} b_m`. A position of `K` beyond the end of `b` removes
nothing and contributes `0` to the sum; for `K = ∅` the result is `b` followed by a block of size
`0`. For a pair `K = {i, j}` with `i < j` it agrees with
[merging two blocks](../../expected-site-frequency-spectrum/merge-blocks.md) at `i` and `j`
([pair case](merge-set-pair.md)). The intended use is a set `K` of at least two positions of `b`:
in the [jump chain](jump-step.md) smaller sets have probability `0`.
