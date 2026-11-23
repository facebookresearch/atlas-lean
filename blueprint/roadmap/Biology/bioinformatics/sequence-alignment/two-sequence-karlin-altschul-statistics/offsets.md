# Diagonal offsets of a grid

For natural numbers `m` and `n`, the offsets are the integers `d` with `-m < d < n`. For
`m, n ≥ 1` these are the `m + n - 1` offsets `-(m - 1), …, n - 1` of the nonempty diagonals of an
`m × n` grid, each diagonal being the set of cells `(i, j)` with `j - i = d`. The set is defined
for all `m` and `n` and has `m + n - 1` elements when `m + n ≥ 1` (none when `m = n = 0`). If
`m = 0` or `n = 0` the grid has no cell, but the set need not be empty: for `m = 0` it is
`1, …, n - 1`.
