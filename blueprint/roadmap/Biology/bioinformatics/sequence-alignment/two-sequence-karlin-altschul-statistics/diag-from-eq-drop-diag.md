# A diagonal from a cell is a suffix of the full diagonal

For a real score `s` on pairs of letters, words `u` and `v` and natural numbers `i` and `j`, the
[diagonal list](diag-from.md) from the cell `(i, j)` is obtained from the
[diagonal of offset](diag.md) `j - i`, which starts at its first cell, by dropping its first
`min(i, j)` entries. So it is a suffix of that diagonal.
