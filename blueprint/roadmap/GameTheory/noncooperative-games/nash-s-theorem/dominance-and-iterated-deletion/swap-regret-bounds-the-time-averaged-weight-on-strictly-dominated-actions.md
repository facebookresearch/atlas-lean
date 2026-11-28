# Swap regret bounds the time-averaged weight on ε-strictly dominated actions

Let $G$ be a finite cost-minimization game played for $T > 0$ rounds with mixed profiles $p^1, \dots, p^T$, and suppose player $i$ has swap regret at most $R$ against its realized expected-cost vectors. If every action in a set $D \subseteq S_i$ is $\varepsilon$-strictly dominated (by a mixed strategy) with $\varepsilon > 0$, then

$$
\frac{1}{T} \sum_{t=1}^{T} \sum_{a \in D} p^t_i(a) \le \frac{R}{\varepsilon T}.
$$

## Proof sketch

Consider the swap function that replaces each dominated action $a \in D$ by its dominating mixture. Its gain is at least $\varepsilon$ times the total weight placed on $D$, and this gain is bounded by the swap regret $R$.

## Depends on

- [Strict, weak and ε-strict dominance by mixed strategies](strict-weak-and-strict-dominance-by-mixed-strategies.md)
- [Swap regret](../../external-and-swap-regret/swap-regret.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007.
