# The RLS estimate minimises the ridge objective

For $\lambda > 0$, the RLS estimate started at $\theta_0 = 0$ and $P_0 = \lambda^{-1} I$ minimises
$\sum_{k<t} (y_{k+1} - \varphi_k^\top \theta)^2 + \lambda |\theta|^2$ over all $\theta$.

## Informally uses

- [Recursive least squares started at $\theta_0 = 0$, $P_0 = \lambda^{-1} I$ is ridge regression](rls-fst-eq-ridge-estimate.md):
  the estimate is the ridge estimate.
- [Closed form of ridge regression](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/ridge-le-ridge-estimate.md): the ridge estimate minimises the ridge objective.
