# Projecting centred data subtracts the projected mean

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, with column means
$\bar x$
([sample means](../principal-component-analysis/col-mean.md))
and
[centred matrix](../principal-component-analysis/center.md)
$X_c = X - \mathbf 1 \bar x^\top$, where $\mathbf 1 \in \mathbb{R}^n$ is the all-ones vector. For
every $n$ and every $w \in \mathbb{R}^p$,

$$X_c w = X w - (\bar x \cdot w)\, \mathbf 1.$$

The projection of each centred sample on $w$ is its projection minus the projection $\bar x \cdot w$
of the mean.
