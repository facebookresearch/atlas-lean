# Collision resistance of Merkle-Damgård with n-bit length fields

Let the chaining values `S` have decidable equality, `0 < n` and `maxLen + n +
n ≤ n * 2 ^ n`. With an `n`-bit length field in the padding and the block
count encoded in one `n`-bit block, every collision finder `A` against the
Merkle-Damgård family over the compression family `C` has advantage at most
that of the reduction `mdReduction` against `C` (the argument of Katz and
Lindell, Theorem 5.4).
