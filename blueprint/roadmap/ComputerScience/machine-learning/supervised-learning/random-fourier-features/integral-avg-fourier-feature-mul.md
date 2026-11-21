# Averaging $D$ random Fourier features is unbiased

Let $(\omega_1, b_1), \dots, (\omega_D, b_D)$ be independent, each with law $p \otimes \mathrm{U}[0, 2\pi]$, and let $z(x) = D^{-1/2}\big(z_{\omega_j, b_j}(x)\big)_{j=1}^D$ be the normalized $D$-dimensional feature map. Then for all inputs $x, y$,

$$
\mathbb{E}\big[z(x)^\top z(y)\big] = \mathbb{E}\Big[\frac1D \sum_{j=1}^D z_{\omega_j, b_j}(x)\, z_{\omega_j, b_j}(y)\Big] = \operatorname{Re} \varphi_p(x - y).
$$

Proof: linearity of expectation and [unbiasedness of one feature](integral-fourier-feature-mul.md).

## Sources

- A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, Advances in Neural Information Processing Systems 20 (NIPS 2007); author PDF at <https://people.eecs.berkeley.edu/~brecht/papers/07.rah.rec.nips.pdf>, Section 3 (the $D$-dimensional map of Algorithm 1, a sample average of the features).
