# Scatter matrix of centred data is $X^\top X - n\bar x \bar x^\top$

Let $X$ be a real $n \times p$ data matrix whose rows $x_1, \dots, x_n$ are the samples, with column
means $\bar x$
([sample means](../../../Probability/linear-models-multivariate/principal-component-analysis/col-mean.md))
and
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$. For every $n$,

$$X_c^\top X_c = X^\top X - n\, \bar x \bar x^\top,$$

that is, $\sum_i (x_i - \bar x)(x_i - \bar x)^\top = \sum_i x_i x_i^\top - n\, \bar x \bar x^\top$.
For $n = 0$ both sides are the zero matrix.
