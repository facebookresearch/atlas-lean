# The kernel Gram matrix of the representer theorem

Let $H$ be a real reproducing kernel Hilbert space of functions on $X$ with kernel $k$. For points
$x_1, \dots, x_n \in X$, the Gram matrix used for kernel ridge regression in the representer
theorem has entries $k(x_i, x_j)$.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Section 2.2
  ($\langle \varphi(x), \varphi(y)\rangle = k(x, y)$).
