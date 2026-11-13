# The front-door adjustment

**The front-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.4): if the
set `M` intercepts every directed path from the treatment node `k` to the outcome node `y`, no
path from `k` to a node of `M` that begins with an arrow into `k` is open (blocked by `∅`), and
every path from a node of `M` to `y` that begins with an arrow into that node is blocked by
`{k}`, then
`P(X_y = v | do(X_k = a)) = ∑_m P(M = m | X_k = a) ∑_{a'} P(X_y = v | X_k = a', M = m) P(X_k = a')`,
assuming `P(X_k = a', M = m) > 0` for all `a'` and `m`.
