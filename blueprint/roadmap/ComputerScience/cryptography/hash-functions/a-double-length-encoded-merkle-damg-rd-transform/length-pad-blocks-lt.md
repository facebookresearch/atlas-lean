# Short messages have few padded blocks

Let `0 < n` and `maxLen + L + n ≤ n * maxBlocks`. If the message `M` has
length less than `maxLen`, then its padded block sequence `padBlocks n L M`
has fewer than `maxBlocks` blocks: the padding adds the `1` bit, fewer than
`n` zeros and an `L`-bit length field.
