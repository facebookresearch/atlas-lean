# Potential function of the l1 interior point method for minimum-cost flow

Fix an integral minimum-cost flow instance (see *Integral minimum-cost flow instances with polynomially bounded data*) with $\mathbf{u}^- < \mathbf{u}^+$ coordinatewise and optimal value $F^*$, and set $\alpha = 1/(1000 \log(mU))$. For a feasible flow $\mathbf{f}$ with $\mathbf{u}^- < \mathbf{f} < \mathbf{u}^+$ and $\mathbf{c}^{\top}\mathbf{f} > F^*$ the potential of $\mathbf{f}$ is

$$
\Phi(\mathbf{f}) = 20m \log\bigl(\mathbf{c}^{\top}\mathbf{f} - F^*\bigr) + \sum_{e \in E}\Bigl((\mathbf{u}^+_e - \mathbf{f}_e)^{-\alpha} + (\mathbf{f}_e - \mathbf{u}^-_e)^{-\alpha}\Bigr).
$$

The first term rewards progress in cost and the second is a barrier for the box constraints whose exponent $\alpha$ makes it far weaker than the logarithmic barrier. The value $F^*$ is unknown to the algorithm; it is handled by binary search over candidate values, since a wrong guess is detected by the potential failing to decrease.

## Depends on

- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
