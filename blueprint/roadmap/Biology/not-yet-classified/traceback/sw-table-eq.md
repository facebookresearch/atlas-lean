# Rows of the Smith–Waterman table

Row `i` of the Smith–Waterman table is
`j ↦ swCellScore (xs.take i) (ys.take j)`, for `i ≤ |xs|` and `j ≤ |ys|`.
