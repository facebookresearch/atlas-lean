# Optimality of stationary policies

Let $M$ be a Markov decision process with finitely many states, finitely many actions (at least one), real rewards and stochastic transition probabilities, and let $0 \le \gamma < 1$. The optimal value $V^*$, the unique solution of Bellman's equation $TV = V$, is the greatest value of a Markov policy: every Markov policy $\pi$ has value at most $V^*$ in every state, and the stationary policy greedy for $V^*$ has value exactly $V^*$. Optimal Markov policies may therefore be taken stationary.

This is the deterministic Markov-policy case, for finite discounted MDPs, of the results listed by Bertsekas for monotone contractive models: Bellman's equation has the unique solution $J^*$, and a stationary policy $\mu^*$ is optimal if and only if $T_{\mu^*} J^* = T J^*$. The comparison is with deterministic Markov policies; randomized and history-dependent policies are not among them. Stationary randomized policies are compared with $V^*$ in [No stochastic policy beats the optimal value](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/stoch-value-le-optimal-value.md).

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Section 1.2.2, results (a) and (b) for models satisfying the monotonicity and contraction Assumptions 1.2.1 and 1.2.2; Example 1.2.2 for finite-state discounted MDPs.
- D. P. Bertsekas, *A Course in Reinforcement Learning*, 2nd ed., Athena Scientific (2026), Section 1.4.1, items (b) and (c).

## Informally uses

- [No Markov policy beats the optimal value](markov-value-le-optimal-value.md)
- [A greedy policy for the optimal value is optimal](../value-iteration/policy-value-greedy.md)
- [The value of a stationary policy](markov-value-const.md)
