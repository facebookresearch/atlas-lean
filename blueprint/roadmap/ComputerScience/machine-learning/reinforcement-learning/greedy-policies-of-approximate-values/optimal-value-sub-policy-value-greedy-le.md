# Loss of a greedy policy for an approximate value

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$, let $0 \le \gamma < 1$, and let $V^*$ be the optimal value. If $|V(s) - V^*(s)| \le d$ for every state $s$ and $\pi = \operatorname{greedy}(V)$ is the policy returned by the [fixed greedy selector](../../../heuristic-search-and-planning/value-iteration/greedy.md) for $V$, then for every state $s$

$$0 \le V^*(s) - V^\pi(s) \le \frac{2\gamma d}{1-\gamma}.$$

Acting greedily on an approximate value loses at most $2\gamma/(1-\gamma)$ times the approximation error; the case $d = 0$ is [A greedy policy for the optimal value is optimal](../../../heuristic-search-and-planning/value-iteration/policy-value-greedy.md). For an action-value estimate $Q$ with $\|Q - Q^*\|_\infty \le d$, the corresponding bound for the policy greedy in $Q$ has constant $2/(1-\gamma)$ (AJKS Lemma 1.11).

## Sources

- S. P. Singh, R. C. Yee, *An upper bound on the loss from approximate optimal-value functions*, Machine Learning 16 (1994), 227–233
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 1.11 (action-value form)

## Background

- [Greedy policy](../../../heuristic-search-and-planning/value-iteration/greedy.md)
