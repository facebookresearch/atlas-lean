# Softmax policy gradient

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$, and let $0 \le \gamma < 1$. For weights $\mu$ and logits $\theta$, the softmax policy gradient in the coordinate $(s,a)$ is $\frac{1}{1-\gamma}\, d^{\pi_\theta}_\mu(s)\, \pi_\theta(a \mid s)\, A^{\pi_\theta}(s,a)$, where $d^{\pi_\theta}_\mu(s) = \sum_{s_0} \mu(s_0) d^{\pi_\theta}_{s_0}(s)$. That this is the gradient of the objective is the [policy gradient theorem for softmax policies](has-deriv-at-softmax-objective.md).

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Lemma C.1
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 12.2
