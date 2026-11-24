# Stock price at a node of the binomial tree

In the binomial tree with initial price `S₀` and real move factors `u` (up) and `d` (down), the
stock price at the node reached by a finite history of moves (listed most recent first) is
defined recursively: it is `S₀` for the empty history, and one further up move multiplies it by
`u`, one further down move by `d`. A history of `n` moves with `k` up moves thus leads to the
price `S₀ * u^k * d^(n - k)`.
