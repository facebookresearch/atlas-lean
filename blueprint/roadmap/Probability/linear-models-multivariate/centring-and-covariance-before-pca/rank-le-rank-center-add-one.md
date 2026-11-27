# Centring lowers the rank by at most one

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with column means
$\bar x$ and
[centred matrix](../../../Probability/linear-models-multivariate/principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$. For every $n$,

$$\operatorname{rank} X \le \operatorname{rank} X_c + 1,$$

because $X = X_c + \mathbf 1 \bar x^\top$ and $\mathbf 1 \bar x^\top$ has rank at most one. The rank
can drop by one: if $n \ge 1$ and all samples equal one nonzero vector, then
$\operatorname{rank} X = 1$ while $X_c = 0$.
