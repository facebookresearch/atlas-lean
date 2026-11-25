# Unbiased empirical estimate of the squared MMD

Let $H$ be a real reproducing kernel Hilbert space of functions on $X$ with kernel $k$. For samples
$x_1, \dots, x_m$ and $y_1, \dots, y_n$ in $X$ of sizes $m, n \ge 2$,

$$\mathrm{MMD}_u^2 = \frac{1}{m(m-1)} \sum_{i \ne j} k(x_i, x_j) + \frac{1}{n(n-1)} \sum_{i \ne j} k(y_i, y_j) - \frac{2}{mn} \sum_{i,j} k(x_i, y_j).$$

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Lemma 6, equation (3).
