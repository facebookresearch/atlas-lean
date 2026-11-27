# Random Fourier features are unbiased

Let $p$ be a probability measure on a real inner product space $E$, and let $\omega \sim p$ and $b$ [uniform on $[0, 2\pi]$](phase-measure.md) be independent. Then for all inputs $x, y \in E$,

$$
\mathbb{E}\big[z_{\omega, b}(x)\, z_{\omega, b}(y)\big] = \operatorname{Re} \varphi_p(x - y),
\qquad \varphi_p(\Delta) = \int e^{i\langle \omega, \Delta\rangle}\, dp(\omega).
$$

If the kernel $k(x, y) = \varphi_p(x - y)$ is real-valued, as for the Gaussian, Laplacian and Cauchy kernels of the source, then $\mathbb{E}[z(x) z(y)] = k(x, y)$: the random features give an unbiased estimate of the kernel.

Proof: averaging over the phase gives $\cos\langle\omega, x - y\rangle$ ([phase average](phase-average-fourier-feature-mul.md)), whose expectation under $p$ is the real part of $\varphi_p(x - y)$.

## Background

- [Bochner's theorem](../../../../Probability/characteristic-functions/bochner-s-theorem/bochner.md): background, how the source obtains $p$ from the kernel: a continuous positive-definite function with value $1$ at $0$ is the characteristic function of a probability measure (the source uses it on $\mathbb{R}^d$).

## Sources

- A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, Advances in Neural Information Processing Systems 20 (NIPS 2007); author PDF at <https://people.eecs.berkeley.edu/~brecht/papers/07.rah.rec.nips.pdf>, Section 3, equation (2) and the real-valued features that follow it; Bochner's theorem is Theorem 1 there.
