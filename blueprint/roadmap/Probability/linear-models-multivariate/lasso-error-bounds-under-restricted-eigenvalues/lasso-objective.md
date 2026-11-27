# Lagrangian Lasso objective

For a design matrix $X \in \mathbb{R}^{n \times d}$, responses $y \in \mathbb{R}^n$ and a
regularization parameter $\lambda$, the Lagrangian (regularized) Lasso objective is

$$\theta \mapsto \frac{1}{2n} \|y - X\theta\|_2^2 + \lambda \|\theta\|_1.$$

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, eq. (11.3).
- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §7.3.

## Background

- [Lasso objective in machine learning](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/lasso.md): the same objective with the unnormalized residual sum of squares, studied there as a MAP estimate.
