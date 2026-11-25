# The biased empirical MMD as a V-statistic

Let $H$ be a real reproducing kernel Hilbert space of functions on $X$ with kernel $k$. For nonempty samples
$x_1, \dots, x_m$ and $y_1, \dots, y_n$ in $X$, the [biased empirical MMD](mmd-biased.md)
satisfies

$$\mathrm{MMD}_b^2 = \frac{1}{m^2} \sum_{i,j} k(x_i, x_j) - \frac{2}{mn} \sum_{i,j} k(x_i, y_j) + \frac{1}{n^2} \sum_{i,j} k(y_i, y_j) .$$

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, equation (5).
