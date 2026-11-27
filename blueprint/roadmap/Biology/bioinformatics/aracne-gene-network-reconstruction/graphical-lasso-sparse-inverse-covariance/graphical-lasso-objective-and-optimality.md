# Graphical lasso objective and optimality conditions

Let $x_1, \dots, x_N \in \mathbb R^p$ be i.i.d. $N(\mu, \Sigma)$ with $\Sigma$ positive definite, and $S$ the empirical covariance matrix (positive semidefinite, possibly singular). For $\rho > 0$ the graphical lasso estimates $\Theta = \Sigma^{-1}$ by

$$\hat\Theta = \arg\max_{\Theta \succ 0}\ \Bigl\{\log\det\Theta - \operatorname{tr}(S\Theta) - \rho \lVert\Theta\rVert_1\Bigr\}, \qquad \lVert\Theta\rVert_1 = \sum_{i,j} |\Theta_{ij}|,$$

the [Gaussian log-likelihood](../../../../Probability/linear-models-multivariate/gaussian-graphical-models/gauss-log-lik.md) $\log\det\Theta - \operatorname{tr}(S\Theta)$ (up to the factor $N/2$ and constants, profiled over $\mu$), plus an $L_1$ penalty. For $\rho > 0$ the maximizer exists and is unique. Since, for $i \ne j$, $\Theta_{ij} = 0$ iff variables $i, j$ are conditionally independent given the rest ([pairwise Markov property](../../../../Probability/linear-models-multivariate/gaussian-graphical-models/cond-indep-fun-iff-inv-apply-eq-zero.md)), the zero pattern of $\hat\Theta$ estimates the Gaussian graphical model.

The problem is convex, and $\hat\Theta$ is optimal iff, with $W = \hat\Theta^{-1}$,

$$W - S - \rho\,\Gamma = 0 \quad\text{for some } \Gamma \text{ with } \Gamma_{ij} = \operatorname{sign}(\hat\Theta_{ij}) \text{ if } \hat\Theta_{ij} \ne 0,\ \Gamma_{ij} \in [-1, 1] \text{ otherwise}.$$

Because $\hat\Theta_{ii} > 0$, this forces $W_{ii} = S_{ii} + \rho$ for every $i$. With different penalties $\rho_{jk} = \rho_{kj}$ on each entry the same holds with $\rho\Gamma$ replaced by $(\rho_{jk}\Gamma_{jk})$; if the diagonal is not penalized, $W_{ii} = S_{ii}$.

## Expansion

$\log\det$ is strictly concave on positive definite matrices, the trace is linear and the penalty convex, so the objective is strictly concave. For $\rho > 0$ and $S \succeq 0$ the objective is at most $\log\det\Theta - \rho\lVert\Theta\rVert_1$, which tends to $-\infty$ as $\Theta$ leaves every compact subset of the positive definite cone, so a maximizer exists. Its subdifferential uses $\nabla_\Theta \log\det\Theta = \Theta^{-1}$, giving the stated stationarity condition; the diagonal entries of a positive definite matrix are positive, so $\Gamma_{ii} = 1$.

## Depends on

- [Gaussian log-likelihood of a precision matrix](../../../../Probability/linear-models-multivariate/gaussian-graphical-models/gauss-log-lik.md)
- [Pairwise Markov property of Gaussian vectors](../../../../Probability/linear-models-multivariate/gaussian-graphical-models/cond-indep-fun-iff-inv-apply-eq-zero.md)

## Sources

- J. Friedman, T. Hastie and R. Tibshirani, "Sparse inverse covariance estimation with the graphical lasso", *Biostatistics* 9 (2008), 432–441, <https://doi.org/10.1093/biostatistics/kxm045> (PMC3019769). Equations (2.1) and (2.6), Remarks 2.1 and 2.2.
