# The MMD of a characteristic kernel separates probability measures

Let $X$ be a measurable space and $H$ a real reproducing kernel Hilbert space of functions on $X$
whose kernel is [characteristic](is-characteristic.md), and let $P$ and $Q$ be probability measures
on $X$ for which the [feature map](feature-map.md) is Bochner integrable. Then
$\mathrm{MMD}(P, Q) = 0$ if and only if $P = Q$. For every kernel the MMD is a pseudometric on such
measures; it is a metric exactly when the kernel is characteristic.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Section 2.2.
