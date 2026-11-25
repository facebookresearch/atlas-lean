# Centring removes a common shift of all samples

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, and write
$Y_c = Y - \mathbf 1 \bar y^\top$ for the
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
of a data matrix $Y$ with column means $\bar y$
([sample means](../../../Probability/linear-models-multivariate/principal-component-analysis/col-mean.md)),
where $\mathbf 1 \in \mathbb{R}^n$ is the all-ones vector. For every $n$ and every
$c \in \mathbb{R}^p$, adding $c$ to every sample does not change the centred matrix:

$$(X + \mathbf 1 c^\top)_c = X_c.$$
