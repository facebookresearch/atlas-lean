# An alignment with few gap columns stays in the band from its start

Along every prefix, the offset difference is at most the starting difference plus the number
of gap columns: an alignment starting at `(i, j)` stays in the band of width `w` as soon as
`|i - j| + gapColumns A ≤ w`.
