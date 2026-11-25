# Integrability of the kernel on a product

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$ with
kernel $k$ and [feature map](../reproducing-kernel/feature-map.md) $\varphi$, and let $P$ and $Q$ be s-finite measures
on $X$ for which $\varphi$ is Bochner integrable. Then $(x, y) \mapsto k(x, y)$ is
$P \otimes Q$-integrable, since $|k(x, y)| \le \|\varphi(x)\|\, \|\varphi(y)\|$.

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample
  test*, Journal of Machine Learning Research 13 (2012), 723–773, proof of Lemma 6.
