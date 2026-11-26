# First largest cell

The position `(i, j)` of the first largest entry of a table in
row-major order (rows top to bottom, each row left to right): `List.argmax` of the entries
`((i, j), T[i][j])` listed in that order, which keeps the first of tied entries. It is `(0, 0)`
when the table has no entry.
