# Optimality of stationary policies

Markov policies choose a decision rule at each stage, possibly a different one each time. Following Bertsekas (*Abstract Dynamic Programming*, 3rd ed., 2022, Section 1.2), the $N$-stage value of a Markov policy $\pi = (\mu_0, \mu_1, \dots)$ is the composition $T_{\mu_0} T_{\mu_1} \cdots T_{\mu_{N-1}} V$ of the policies' Bellman operators applied to a terminal value $V$, and its value is the limit as $N \to \infty$. For a finite discounted MDP the limit exists and does not depend on $V$; no Markov policy beats the optimal value, and the stationary policy greedy for the optimal value attains it. So optimal policies may be taken stationary. Over a finite horizon $N$ the same comparison shows that the DP algorithm is optimal: the value iterate $T^N V$ is the best $N$-stage value, attained by the policy that acts greedily for $T^{N-1-k} V$ at stage $k$. The policies compared are deterministic Markov policies; randomized and history-dependent policies are not among them.

- [N-stage value of a Markov policy](n-stage-value.md)
- [Value of a Markov policy](markov-value.md)
- [Appending a stage at the end](n-stage-value-succ.md)
- [N-stage values of a stationary policy](n-stage-value-const.md)
- [A Markov policy does no better than value iteration over N stages](n-stage-value-le-iterate.md)
- [The dynamic programming policy](dp-policy.md)
- [The dynamic programming policy attains the value iterate](n-stage-value-dp-policy.md)
- [Optimality of the dynamic programming algorithm](is-greatest-n-stage-value.md)
- [The terminal value is forgotten geometrically](dist-n-stage-value-le.md)
- [The N-stage values of a Markov policy converge](tendsto-n-stage-value.md)
- [The value of a stationary policy](markov-value-const.md)
- [No Markov policy beats the optimal value](markov-value-le-optimal-value.md)
- [Optimality of stationary policies](is-greatest-markov-value.md)

## Related topics

- [Value iteration](../value-iteration/README.md)
- [Policy iteration](../policy-iteration/README.md)
- [Stochastic policies and discounted occupancy](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/README.md)
- [Optimal stopping and the Snell envelope](../../../Probability/martingales/optimal-stopping-and-the-snell-envelope/README.md): backward induction for optimal stopping, the stop-or-continue case of the finite-horizon DP algorithm.
