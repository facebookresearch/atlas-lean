# The biased empirical MMD is the distance between empirical mean embeddings

Let $H$ be a real reproducing kernel Hilbert space of functions on $X$. For nonempty samples
$x_1, \dots, x_m$ and $y_1, \dots, y_n$ in $X$, the [biased empirical MMD](mmd-biased.md) is
$\mathrm{MMD}_b = \|\mu_X - \mu_Y\|$, the distance between the [empirical mean
embeddings](empirical-embedding.md).

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Section 2.2, before
  equation (5).
