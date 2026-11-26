# Collision resistance of the full Merkle-Damgård hash family

Let the chaining values `S` have decidable equality. Let `0 < n`, let
`lenBlock` separate block counts below `maxBlocks` (`lenBlock a = lenBlock b`
with `a, b < maxBlocks` implies `a = b`), and let `maxLen + L + n ≤ n *
maxBlocks`. Then every collision finder `A` against `mdFamily C` has advantage
at most that of `mdReduction` against the compression family `C` (the argument
of Katz and Lindell, Theorem 5.4).
