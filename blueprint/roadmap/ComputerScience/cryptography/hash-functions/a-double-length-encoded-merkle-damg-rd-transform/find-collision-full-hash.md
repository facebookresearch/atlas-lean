# Extracting a compression collision from a full-hash collision

Let the chaining values `S` have decidable equality. Let `0 < n`, let
`lenBlock` separate block counts below `maxBlocks` (`lenBlock a = lenBlock b`
with `a, b < maxBlocks` implies `a = b`), and let `maxLen + L + n ≤ n *
maxBlocks`. If two distinct messages `M ≠ M'` of length less than `maxLen`
have equal full hashes, then `findCollision` applied to their padded block
sequences returns a collision of the compression function `h` (the argument of
Katz and Lindell, Theorem 5.4).
