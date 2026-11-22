# Biased empirical MMD

Let $H$ be a real reproducing kernel Hilbert space of functions on $X$. For nonempty samples
$x_1, \dots, x_m$ and $y_1, \dots, y_n$ in $X$ ($m, n \ge 1$),

$$\mathrm{MMD}_b = \sup_{\|f\|_H \le 1} \Big(\frac{1}{m} \sum_{i=1}^m f(x_i) - \frac{1}{n} \sum_{j=1}^n f(y_j)\Big).$$

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, equation (2), with $\mathcal F$
  the unit ball of $H$.
