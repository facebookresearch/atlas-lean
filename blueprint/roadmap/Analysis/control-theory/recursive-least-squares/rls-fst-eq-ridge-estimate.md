# Recursive least squares started at $\theta_0 = 0$, $P_0 = \lambda^{-1} I$ is ridge regression

For $\lambda > 0$ and every $t$, the RLS estimate started at $\theta_0 = 0$ and $P_0 = \lambda^{-1} I$ equals the
ridge estimate $(X^\top X + \lambda I)^{-1} X^\top Y$, where $X$ is the
[design matrix of the first $t$ regressors](design-matrix.md) and $Y_k = y_{k+1}$.

## Informally uses

- [Recursive least squares equals batch regularised least squares](rls-fst-eq.md): with $\theta_0 = 0$ and
  $P_0^{-1} = \lambda I$ the batch formula is the ridge formula, since $X^\top X = \sum_{k<t} \varphi_k \varphi_k^\top$
  and $X^\top Y = \sum_{k<t} y_{k+1} \varphi_k$.

## Background

- [Ridge estimate](../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/ridge-estimate.md): the closed form identified here.
