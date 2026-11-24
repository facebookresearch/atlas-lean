# No stochastic policy beats the optimal value

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. Assume $A$ is nonempty and let $V^*$ be the optimal value (the solution of the Bellman optimality equation). For every stationary stochastic policy $\pi$, $V^\pi(s) \le V^*(s)$ for every state $s$. With [A greedy policy for the optimal value is optimal](../../../heuristic-search-and-planning/value-iteration/policy-value-greedy.md), the optimum over stationary stochastic policies is attained by a deterministic one.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Theorem 1.7 (stated there for all non-stationary randomized policies; only stationary policies are covered here)

## Informally uses

- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md): the proof compares the policy's Bellman update with the Bellman optimality equation of $V^*$.
