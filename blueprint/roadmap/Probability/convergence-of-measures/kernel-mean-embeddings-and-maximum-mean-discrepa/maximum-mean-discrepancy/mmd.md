# Maximum mean discrepancy over the unit ball of an RKHS

Let $X$ be a measurable space and $H$ a real reproducing kernel Hilbert space of functions on $X$.
For measures $P$ and $Q$ on $X$,

$$\mathrm{MMD}(P, Q) = \sup_{\|f\|_H \le 1} \Big(\int f \, dP - \int f \, dQ\Big),$$

the supremum of a set of reals (taken to be $0$ if it is unbounded), with each integral read as
$0$ when $f$ is not integrable.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Definition 2, equation (1), with
  $\mathcal F$ the unit ball of $H$.
