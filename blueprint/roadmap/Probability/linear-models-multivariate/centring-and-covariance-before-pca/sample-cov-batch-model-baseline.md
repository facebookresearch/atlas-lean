# Sample covariance of the additive design does not depend on $\mu$

Let $X = E + \mathbf 1 \mu^\top + b \beta^\top + s \delta^\top$ be the
[additive design](batch-model.md) with residual matrix $E \in \mathbb{R}^{n \times p}$, baseline
$\mu \in \mathbb{R}^p$, covariates $b, s \in \mathbb{R}^n$ and effects
$\beta, \delta \in \mathbb{R}^p$. For every $n$ and all these arguments, replacing the baseline
$\mu$ by any $\mu' \in \mathbb{R}^p$ leaves the
[sample covariance matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/sample-cov.md)
of $X$ unchanged, because $\mathbf 1 \mu^\top$ shifts all samples by the same vector $\mu$.
