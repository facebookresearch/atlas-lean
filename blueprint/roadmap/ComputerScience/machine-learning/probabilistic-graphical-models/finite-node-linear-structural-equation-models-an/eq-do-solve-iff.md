# `do(X_k = a)` replaces the `k`-th structural equation by `X_k = a`

For a recursive
`B`, `doSolve B k a e` is the unique vector that equals `a` at `k` and satisfies the original
structural equation `X_i = (B X)_i + e_i` at every other node.
