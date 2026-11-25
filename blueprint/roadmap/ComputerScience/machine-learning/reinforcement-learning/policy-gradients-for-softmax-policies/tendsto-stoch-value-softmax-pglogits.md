# Global convergence of softmax policy gradient

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$, and let $0 \le \gamma < 1$. Assume the rewards lie in $[0,1]$, $\mu$ is a probability distribution with $\mu(s) > 0$ for every state, and $0 < \eta \le (1-\gamma)^3/8$. Then the values of the softmax policy gradient iterates converge to the optimal value: $V^{\pi_{\theta_t}}(s) \to V^*(s)$ as $t \to \infty$, for every state $s$. No rate is claimed; compare the dimension-free rate of [natural policy gradient](../natural-policy-gradient/optimal-value-sub-stoch-value-npg-policy.md). The iteration here starts from $\theta_0 = 0$, a special case: the source fixes no initialization, and its proof works from any $\theta_0$.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Theorem 5.1
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Theorem 12.3
