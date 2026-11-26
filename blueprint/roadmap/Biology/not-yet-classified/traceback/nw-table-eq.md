# Rows of the Needleman–Wunsch table

Row `i` of the Needleman–Wunsch table is
`j ↦ nwScore (xs.take i) (ys.take j)`, for `i ≤ |xs|` and `j ≤ |ys|`.
