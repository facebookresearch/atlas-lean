# Inner product of two mean embeddings

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$ with
kernel $k$ and [feature map](../reproducing-kernel/feature-map.md) $\varphi$, and let $P$ and $Q$ be measures on $X$
for which $\varphi$ is Bochner integrable. Then the [mean embeddings](mean-embedding.md) satisfy

$$\langle \mu_P, \mu_Q\rangle = \int \Big(\int k(x, y)\, dP(x)\Big) dQ(y) .$$

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, proof of Lemma 6.
