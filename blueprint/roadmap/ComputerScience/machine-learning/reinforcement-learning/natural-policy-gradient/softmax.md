# Softmax policy

The softmax policy of logits $\theta : S \times A \to \mathbb{R}$ (with $A$ finite and nonempty) is $\pi_\theta(a \mid s) = \exp\theta(s,a) / \sum_b \exp\theta(s,b)$.

## Sources

- A. Agarwal, S. M. Kakade, J. D. Lee, G. Mahajan, *On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*, JMLR 22(98), 2021, arXiv:1908.00261, equation (3)
