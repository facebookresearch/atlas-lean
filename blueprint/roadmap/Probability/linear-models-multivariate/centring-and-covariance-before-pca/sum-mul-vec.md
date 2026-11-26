# Projections of the samples sum to $n$ times the projected mean

Let $X$ be a real $n \times p$ data matrix whose rows $x_1, \dots, x_n$ are the samples, with column
means $\bar x$
([sample means](../principal-component-analysis/col-mean.md)),
and let $w \in \mathbb{R}^p$. For every $n$,

$$\sum_{i=1}^n (X w)_i = n\, (\bar x \cdot w).$$

So for $n \ge 1$ the projections $(X w)_i = x_i \cdot w$ of the samples on $w$ have mean
$\bar x \cdot w$.
