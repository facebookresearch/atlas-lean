# Columns of the centred data matrix sum to zero

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with column means
$\bar x$
([sample means](../../../Probability/linear-models-multivariate/principal-component-analysis/col-mean.md))
and
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$, where $\mathbf 1 \in \mathbb{R}^n$ is the all-ones vector. For
every $n$, every column of $X_c$ sums to zero:

$$\mathbf 1^\top X_c = 0, \qquad \sum_{i=1}^n (X_{ij} - \bar x_j) = 0 \text{ for every } j.$$

For $n = 0$ the sums are empty.
