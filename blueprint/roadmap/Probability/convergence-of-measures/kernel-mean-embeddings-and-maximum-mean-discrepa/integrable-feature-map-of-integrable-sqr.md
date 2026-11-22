# Existence of the kernel mean embedding

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$ with
kernel $k$ and [feature map](feature-map.md) $\varphi$, and $P$ a measure on $X$. If $\varphi$ is
$P$-almost everywhere strongly measurable and $\int \sqrt{k(x, x)}\, dP(x) < \infty$, then
$\varphi$ is Bochner integrable, so the mean embedding $\mu_P \in H$ exists and has the
[reproducing property](inner-mean-embedding.md). The paper assumes $k$ measurable; the
measurability hypothesis here is the one Bochner integration needs.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Lemma 3.
