# Confounded design: sample covariance depends only on $\beta + \delta$

Let $E \in \mathbb{R}^{n \times p}$ and $b \in \mathbb{R}^n$, and write
$X(\mu, \beta, \delta) = E + \mathbf 1 \mu^\top + b \beta^\top + b \delta^\top$ for the confounded
[additive design](batch-model.md), in which the batch and the biological covariate are both $b$. If
$\beta + \delta = \beta' + \delta'$, then for all baselines $\mu, \mu' \in \mathbb{R}^p$ the data
matrices $X(\mu, \beta, \delta)$ and $X(\mu', \beta', \delta')$ have the same
[sample covariance matrix](../principal-component-analysis/sample-cov.md).
This holds for every $n$.
