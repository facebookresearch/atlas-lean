# Population MMD in terms of the kernel

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$ with
kernel $k$, and $P$, $Q$ s-finite measures on $X$ for which the [feature map](feature-map.md) is
Bochner integrable. Then

$$\mathrm{MMD}(P, Q)^2 = \int k \, d(P \otimes P) - 2 \int k \, d(P \otimes Q) + \int k \, d(Q \otimes Q):$$

with $x, x'$ independent with law $P$ and $y, y'$ independent with law $Q$,
$\mathrm{MMD}(P, Q)^2 = \mathbb{E}\, k(x, x') - 2\, \mathbb{E}\, k(x, y) + \mathbb{E}\, k(y, y')$.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Lemma 6.
