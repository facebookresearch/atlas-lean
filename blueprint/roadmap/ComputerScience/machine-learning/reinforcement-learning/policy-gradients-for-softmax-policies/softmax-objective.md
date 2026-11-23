# Softmax policy objective

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and stochastic transition probabilities $P(s,a,s')$, and let $0 \le \gamma < 1$. For weights $\mu$ on $S$ and logits $\theta$, the objective of softmax policy optimization is $V^{\pi_\theta}(\mu) = \sum_{s_0} \mu(s_0)\, V^{\pi_\theta}(s_0)$.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, Section 2
