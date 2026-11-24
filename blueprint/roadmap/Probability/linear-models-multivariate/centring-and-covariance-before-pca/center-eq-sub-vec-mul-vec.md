# The centred data matrix is $X - \mathbf{1}\bar x^\top$

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with column means
$\bar x \in \mathbb{R}^p$
([sample means](../../../Probability/linear-models-multivariate/principal-component-analysis/col-mean.md)),
and let $\mathbf 1 \in \mathbb{R}^n$ be the all-ones vector. The
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c$, with entries $X_{ij} - \bar x_j$, is

$$X_c = X - \mathbf 1 \bar x^\top.$$
