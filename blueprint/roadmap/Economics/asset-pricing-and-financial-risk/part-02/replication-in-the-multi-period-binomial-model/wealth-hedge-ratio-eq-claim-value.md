# Delta-hedging wealth tracks the claim value at every node

Let `S₀`, `u`, `d` be nonzero with `u ≠ d`, and let `R ≠ 0`; the no-arbitrage condition
`d < R < u` is not assumed. Fix a claim `V` on histories of moves and a horizon `N`, and let
`v_k(s)` be its backward-induction value with `k` periods left: `v_0 = V` and
`v_{k+1}(s) = (q * v_k(s, up) + (1 - q) * v_k(s, down)) / R` with `q = (R - d) / (u - d)`. The
self-financing strategy that starts at the root with capital `v_N` and holds at each node the
delta-hedging ratio (the change in claim value divided by the change in stock price across the
two successor nodes) has wealth `v_{N - n}(s)` at every history `s` of length `n ≤ N`.
