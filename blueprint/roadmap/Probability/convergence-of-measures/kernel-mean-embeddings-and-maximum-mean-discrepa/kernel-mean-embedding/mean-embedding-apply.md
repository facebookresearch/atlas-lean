# The mean embedding as a function

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$ with
kernel $k$ and [feature map](../reproducing-kernel/feature-map.md) $\varphi$, and $P$ a measure on $X$ for which
$\varphi$ is Bochner integrable. Then the [mean embedding](mean-embedding.md) is the function
$\mu_P(t) = \int k(t, x)\, dP(x)$.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Lemma 3 and its proof.
