# Characterization of characteristic translation-invariant kernels

Let $d \ge 1$ and let $H$ be a real reproducing kernel Hilbert space of functions on
$\mathbb{R}^d$ whose kernel is $k(x, y) = \psi(x - y)$ with
$\psi(x) = \int e^{-i \langle x, \omega\rangle} \, d\Lambda(\omega)$ for a finite Borel measure
$\Lambda$, so that $\psi$ is a bounded continuous real positive-definite function (equation (11)
of the source). Then $k$ is [characteristic](is-characteristic.md) if and only if the support of
$\Lambda$ is all of $\mathbb{R}^d$.

The Gaussian kernel $e^{-\|x - y\|^2 / (2\sigma^2)}$ and the Laplacian kernel have spectral measures with full support and are characteristic on all of $\mathbb{R}^d$, with no compactness assumption, which [the universal-kernel criterion](mmd-eq-zero-iff-of-universal.md) does not give. The sinc kernel, whose spectrum is an interval, is not characteristic: two different laws whose characteristic functions agree on that interval have the same embedding.

The hypothesis $d \ge 1$ excludes the one-point space $\mathbb{R}^0$, on which every kernel is characteristic while the zero measure has empty support.

## Informally uses

- [Population MMD in terms of the kernel](mmd-sq-eq.md): the paper's Corollary 4(i), used for sufficiency, rewrites this kernel expression (their equation (9)) of $\mathrm{MMD}^2$ through Bochner's representation of $\psi$ as $\int |\varphi_P - \varphi_Q|^2 \, d\Lambda$.

## Sources

- B. K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Schölkopf and G. R. G. Lanckriet, *Hilbert
  space embeddings and metrics on probability measures*, Journal of Machine Learning Research 11
  (2010), 1517–1561, Theorem 9.
