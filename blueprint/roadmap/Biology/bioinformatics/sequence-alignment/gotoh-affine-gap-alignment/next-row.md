# Gotoh table row from the previous row

The row of `a :: xs` from the row `prev` of `xs`, over the remaining suffixes of `ys`, longest
first; each cell uses the cell to its right in the same row. A row `prev` that is too short gives
junk cells (this does not happen for rows of the table, `nextRow_eq`).
