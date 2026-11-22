# Inner product of mean embeddings as an expectation over independent copies

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$ with
kernel $k$ and [feature map](feature-map.md) $\varphi$, and let $P$ and $Q$ be s-finite measures
on $X$ for which $\varphi$ is Bochner integrable. Then the [mean embeddings](mean-embedding.md)
satisfy

$$\langle \mu_P, \mu_Q\rangle = \int k(x, y)\, d(P \otimes Q)(x, y) .$$

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, proof of Lemma 6.
