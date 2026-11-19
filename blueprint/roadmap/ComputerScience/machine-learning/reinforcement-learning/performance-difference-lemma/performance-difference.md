# Performance difference lemma

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For all stochastic policies $\pi, \pi'$ and every state $s_0$,

$$V^{\pi'}(s_0) - V^\pi(s_0) = \frac{1}{1-\gamma}\, \mathbb{E}_{s \sim d^{\pi'}_{s_0}}\, \mathbb{E}_{a \sim \pi'(\cdot \mid s)} \bigl[A^\pi(s,a)\bigr].$$

The value gap between two policies is the advantage of one over the other, averaged along the state distribution of the first. It underlies policy iteration, conservative policy iteration and the analysis of policy gradient methods. The [policy improvement theorem](../../../heuristic-search-and-planning/policy-iteration/policy-value-le-policy-value-improve.md) for deterministic policies is a special case of its consequence [policy improvement for stochastic policies](stoch-value-le-of-sum-prob-mul-advantage.md).

## Sources

- S. Kakade, J. Langford, *Approximately Optimal Approximate Reinforcement Learning*, ICML 2002
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 1.16
- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Lemma 3.2
