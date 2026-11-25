# Inner product of empirical mean embeddings

Let $H$ be a real reproducing kernel Hilbert space of functions on $X$ with kernel $k$. For nonempty samples
$x_1, \dots, x_m$ and $y_1, \dots, y_n$ in $X$ ($m, n \ge 1$), the [empirical mean embeddings](empirical-embedding.md)
satisfy

$$\langle \mu_X, \mu_Y \rangle = \frac{1}{mn} \sum_{i=1}^m \sum_{j=1}^n k(x_i, y_j).$$

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, derivation of equation (5).
