# Block Count Len Block

A length block for `MerkleDamgard.hash`: the block count as an `n`-bit little-endian number.
In `fullHash` it is the second length encoding, after the bit length inside the padding; Katz and
Lindell's Construction 5.3 has no block-count block.
