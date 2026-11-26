# Multi-scale multiplicative weights for swap regret

Fix $n$ actions, a target $\varepsilon$, $S = \log_2(1/\varepsilon) + 1$ and block size $H = 4\log(n)\,2^{2S} = \Theta(\log n/\varepsilon^2)$, and run for $T = H^{2^S}$ days. The **multi-scale multiplicative weights** algorithm maintains $2^S$ threads; thread $k \in [2^S]$ restarts every $T/H^k$ days, and during each restart, which lasts $H^k$ days, it groups $H^{k-1}$ consecutive days into one meta-day and runs multiplicative weights for $H$ meta-day steps on the meta-day average losses. On each day the learner plays the uniform mixture of the current distributions of all threads.

## Depends on

- [The $\sqrt{T}$ regret bound of Hedge](../hedge-algorithm/regret-le-two-sqrt.md)
- [TreeSwap: swap regret from external regret on a tree of restarts](treeswap-algorithm.md)

## Sources

- B. Peng, A. Rubinstein, "Fast Swap Regret Minimization and Applications to Approximate Correlated Equilibria", STOC (2024), arXiv:2310.19647.
