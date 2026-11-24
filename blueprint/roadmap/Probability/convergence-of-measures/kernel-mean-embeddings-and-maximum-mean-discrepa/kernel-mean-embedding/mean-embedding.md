# Kernel mean embedding

Let $X$ be a measurable space and $H$ a real reproducing kernel Hilbert space of functions on $X$
with [feature map](../reproducing-kernel/feature-map.md) $\varphi$. The mean embedding of a measure $P$ on $X$ is the
Bochner integral $\mu_P = \int \varphi(x)\, dP(x) \in H$ (which is $0$ when $\varphi$ is not
integrable); it is the element of $H$ representing expectation under $P$ when $\varphi$ is
integrable ([reproducing property](inner-mean-embedding.md)).

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, Section 2.2 and Lemma 3.
