# Every deterministic ski-rental strategy is a rent-then-buy threshold

For every deterministic online strategy for ski rental with purchase price $B$ there is a threshold $t \in \mathbb{N} \cup \{\infty\}$ such that on every season of $n$ days the strategy rents on days $1, \dots, \min(n, t)$ and buys on day $t + 1$ if $t < n$; its cost is $n$ if $n \le t$ and $t + B$ otherwise. Consequently every randomized strategy against an oblivious adversary induces a probability distribution on thresholds, and its expected cost on $n$ days is the corresponding average.

## Proof sketch

Each request is identical, so the strategy's decision on day $i$ depends only on $i$ (whether it has already bought); the first day on which it buys defines $t$.

## Depends on

- [Online request-serving problem and competitive ratio](../competitive-analysis/online-problem-and-competitive-ratio.md)
- [Deterministic ski-rental strategy](../ski-rental-problem/strategy.md)

## Sources

- A. R. Karlin, M. S. Manasse, L. Rudolph and D. D. Sleator, "Competitive Snoopy Caching", Algorithmica 3, 1988.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
