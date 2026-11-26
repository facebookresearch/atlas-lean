# Global convergence of natural policy gradient

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. Assume all rewards lie in $[0, 1]$ and $A$ is nonempty, and run natural policy gradient with softmax policies from $\theta_0 = 0$ with step size $\eta > 0$. For every $T \ge 1$ and every state $s_0$,

$$V^*(s_0) - V^{\pi_T}(s_0) \le \frac{\log |A|}{\eta T} + \frac{1}{(1-\gamma)^2 T}.$$

Averaging over a start distribution $\rho$ gives the published form $V^{\pi_T}(\rho) \ge V^*(\rho) - \log|A|/(\eta T) - 1/((1-\gamma)^2 T)$. The rate depends on neither the number of states nor a distribution mismatch coefficient, although $V^{\pi_\theta}$ is not concave in $\theta$. The proof combines the performance difference lemma against an optimal deterministic policy with the regret analysis of multiplicative weights, as for the [Hedge algorithm](../../online-learning-and-boosting/hedge-algorithm/README.md), run in every state.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Theorem 5.3
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Theorem 12.7

## Background

- [Optimal value of a discounted Markov decision process](../../../heuristic-search-and-planning/value-iteration/optimal-value.md): the comparator $V^*$.
