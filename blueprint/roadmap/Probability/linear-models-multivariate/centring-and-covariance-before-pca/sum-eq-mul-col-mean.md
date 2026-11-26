# Column sums are $n$ times the column means

Let $X$ be a real $n \times p$ data matrix whose rows are the $n$ samples, and let
$\bar x_j = \frac1n \sum_i X_{ij}$ be the
[sample mean](../principal-component-analysis/col-mean.md)
of column $j$. For every $n$ and every column $j$,

$$\sum_{i=1}^n X_{ij} = n\, \bar x_j.$$

For $n = 0$ both sides are $0$.
