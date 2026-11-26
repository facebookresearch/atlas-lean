# Contracting along a path with an inserted vertex

Let `f k` be a function of the two
endpoints of the `k`-th step of a path. Along the path obtained from `x` by inserting `v` after
`xₗ`, contracting the steps `l` and `l + 1` gives the entries `f ((l + 1).succAbove k)` read
along `x`, except in position `l`, which holds `op (f l xₗ v) (f (l + 1) v xₗ₊₁)`.
