# Rank iterate

Rank increases along find paths in a union-find forest:
`p` is the parent function on `α` (roots are fixed points),
`r` assigns ranks. If every non-root has rank below its parent's
rank, then walking `k` parent steps from `x` (through non-roots)
raises the rank by at least `k`. This is the invariant that
makes `find` logarithmic once ranks are `O(log n)`.
