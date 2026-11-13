# Auxiliary row computation for the Smith–Waterman table

The cells `H[i+1][j+1], H[i+1][j+2], …` of a row from the remaining letters `b :: ys` of the
second sequence, the remaining cells `up :: prev` of the previous row, the previous row's cell
`diag` to the upper left and the cell `left` just computed. A previous row that is too short ends
the row early (this does not happen for rows of the table, `nextRow_eq`).
