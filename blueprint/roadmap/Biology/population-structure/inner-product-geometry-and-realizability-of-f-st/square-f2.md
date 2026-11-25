# Squared distances between the corners of the unit square

The matrix on four populations `0, 1, 2, 3` of the squared Euclidean distances between the corners
`(0, 0)`, `(1, 0)`, `(0, 1)`, `(1, 1)` of the unit square: its rows are `(0, 1, 1, 2)`,
`(1, 0, 2, 1)`, `(1, 2, 0, 1)` and `(2, 1, 1, 0)`. It is the f2 matrix of a drift model with two
edges of length `1` and lineage weight vectors `(0, 0)`, `(1, 0)`, `(0, 1)`, `(1, 1)`, so it is
[realizable by a drift model](is-f2-realizable.md), but it violates the four-point condition, so it
is not a tree metric.
