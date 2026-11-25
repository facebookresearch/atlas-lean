# Discounted state occupancy of a policy

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. The discounted state occupancy of a stochastic policy $\pi$ from $s_0$ is $d^\pi_{s_0}(s) = (1-\gamma)\sum_{t \ge 0} \gamma^t \Pr^\pi(s_t = s \mid s_0)$, the discounted visitation of the Markov chain $P^\pi$.

## Related topics

- [Discounted state-action occupancy of a row-stochastic policy](../stochastic-policies-and-discounted-occupancy/occupancy.md): the state-action occupancy from an initial weighting, with the policy given as a row-stochastic matrix.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, equation (0.9)
- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, equation (4)
