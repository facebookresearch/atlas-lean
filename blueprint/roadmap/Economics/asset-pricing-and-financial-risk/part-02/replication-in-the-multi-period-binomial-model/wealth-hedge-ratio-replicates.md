# Delta hedging replicates every path-dependent claim

In the multi-period binomial model (Cox, Ross and Rubinstein 1979) with `S₀`, `u`, `d` nonzero,
`u ≠ d` and `R ≠ 0` (the no-arbitrage condition `d < R < u` is not assumed), every
path-dependent claim `V` paid at horizon `N` is replicated by the self-financing delta-hedging
strategy started with its backward-induction value at the root (discounted risk-neutral averages
with `q = (R - d) / (u - d)`), which holds at each node the change in claim value divided by the
change in stock price across the two successor nodes: the terminal wealth equals `V(s)` on every
history `s` of `N` moves.
