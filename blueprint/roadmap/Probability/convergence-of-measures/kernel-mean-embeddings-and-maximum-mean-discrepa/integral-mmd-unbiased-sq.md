# The unbiased MMD statistic is unbiased

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$, and
$P$, $Q$ probability measures on $X$ for which the [feature map](feature-map.md) is Bochner
integrable. Let $m, n \ge 2$, let $x_1, \dots, x_m$ be i.i.d. with law $P$ and $y_1, \dots, y_n$
i.i.d. with law $Q$, the two samples independent. Then the [unbiased statistic](mmd-unbiased-sq.md)
satisfies $\mathbb{E}[\mathrm{MMD}_u^2] = \mathrm{MMD}(P, Q)^2$.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Lemma 6.
