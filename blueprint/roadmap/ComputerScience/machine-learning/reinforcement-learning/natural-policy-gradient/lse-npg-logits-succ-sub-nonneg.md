# The NPG normalizer is at least one

Along natural policy gradient, $\log Z_t(s) = \operatorname{lse}_{\theta_{t+1}}(s) - \operatorname{lse}_{\theta_t}(s) \ge 0$ for every state $s$, where $Z_t(s) = \sum_a \pi_t(a \mid s) \exp(\eta A^{\pi_t}(s,a)/(1-\gamma))$.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, proof of Lemma 5.2
