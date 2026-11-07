# One row of the table

From the row of the prefix `px`, `nextRow` computes the row of
`px ++ [a]`: the cells `nwScore (px ++ [a]) py` for the prefixes `py` of `ys`, shortest first.
