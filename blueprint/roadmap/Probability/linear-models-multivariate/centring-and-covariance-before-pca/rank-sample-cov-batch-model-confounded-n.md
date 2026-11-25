# Noiseless confounded design: sample covariance has rank at most one

Let $\mu, \beta, \delta \in \mathbb{R}^p$ and $b \in \mathbb{R}^n$, and let
$X = \mathbf 1 \mu^\top + b \beta^\top + b \delta^\top$ be the confounded
[additive design](batch-model.md) without residual noise ($E = 0$). For every $n$, its
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
has rank at most one: it is a scalar multiple of $(\beta + \delta)(\beta + \delta)^\top$.
