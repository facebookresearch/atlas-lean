# Softmax policy gradient ascent

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$, and let $0 \le \gamma < 1$. Gradient ascent on the softmax objective with step size $\eta$ starts from $\theta_0 = 0$ and updates $\theta_{t+1} = \theta_t + \eta\, \nabla_\theta V^{\pi_{\theta_t}}(\mu)$, the gradient being written in the closed form of the softmax policy gradient.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, equation (11)
- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Chapter 12, equation (0.2)
