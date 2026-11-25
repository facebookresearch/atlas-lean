# The MMD is the distance between mean embeddings

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$, and
$P$, $Q$ measures on $X$ for which the [feature map](../reproducing-kernel/feature-map.md) is Bochner integrable. Then
$\mathrm{MMD}(P, Q) = \|\mu_P - \mu_Q\|$, with $\mu_P, \mu_Q$ the [mean
embeddings](../kernel-mean-embedding/mean-embedding.md).

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Lemma 4.
