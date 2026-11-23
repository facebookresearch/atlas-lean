# Letter-disjoint diagonals are independent

The diagonal with offset `-i` (starting at
`(i, 0)`) and the diagonal with offset `j` (starting at `(0, j)`) read disjoint sets of letters
when the first ends before column `j` and the second ends before row `i`; their score sequences
are then independent. Diagonals that share a letter are in general dependent (see the test
file).
