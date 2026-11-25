# Entries of the K80 rate matrix

For every real `κ`, the
[K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md) with
transition/transversion ratio `κ` has entry `-(κ + 2)/4` on the diagonal, `κ/4` at `(i, j)` for
distinct indices `i`, `j` of the same parity, and `1/4` at `(i, j)` for indices of opposite parity.
With the nucleotides indexed `0 = A`, `1 = C`, `2 = G`, `3 = T`, the pairs of distinct indices of
the same parity are the transitions, between `A` and `G` and between `C` and `T`; the other
off-diagonal pairs are the transversions.
