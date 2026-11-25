# Policy gradient theorem for softmax policies

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$, and let $0 \le \gamma < 1$. For weights $\mu$, logits $\theta$, a state $s$ and an action $a$,

$$\frac{\partial V^{\pi_\theta}(\mu)}{\partial \theta(s,a)} = \frac{1}{1-\gamma}\, d^{\pi_\theta}_\mu(s)\, \pi_\theta(a \mid s)\, A^{\pi_\theta}(s,a).$$

The source derives it from the general policy gradient formula; dividing the [performance difference lemma](../performance-difference-lemma/performance-difference.md) for $\pi_\theta$ and a perturbed policy by the perturbation is another route.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Lemma C.1
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 12.2
