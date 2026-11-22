# Greedy policies of value iteration are near-optimal

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$, let $0 \le \gamma < 1$, and let $V^*$ be the optimal value. Let $T$ be the Bellman optimality operator, $V$ any function on $S$, and $\pi_n$ a greedy policy for the $n$-th value iterate $T^n V$. Then for every state $s$

$$V^*(s) - V^{\pi_n}(s) \le \frac{2\gamma}{1-\gamma} \cdot \frac{\gamma^n\, \|V - TV\|_\infty}{1-\gamma}.$$

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Theorem 1.12 (stated there for Q-value iteration)

## Informally uses

- [A priori error bound for value iteration](../../../heuristic-search-and-planning/value-iteration/dist-value-iteration-le.md)
