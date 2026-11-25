# The full Merkle-Damgård hash preserves collision resistance

Let the chaining values `S` have decidable equality and the coins `R` be
finite and nonempty. Let `0 < n`, let `lenBlock` separate block counts below
`maxBlocks` (`lenBlock a = lenBlock b` with `a, b < maxBlocks` implies `a =
b`), and let `maxLen + L + n ≤ n * maxBlocks`. For every adversary `A : R →
List Bool × List Bool` with uniform coins, the probability that `A` finds a
collision of the full hash among messages shorter than `maxLen` is at most the
probability that the compression-collision finder `reduction ∘ blockAdversary`
finds a collision of `h` (the argument of Katz and Lindell, Theorem 5.4).
