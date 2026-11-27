# Nyquist–Shannon sampling theorem (Whittaker–Shannon interpolation formula)

Let
$\operatorname{sinc}(x) = \frac{\sin x}{x}$ for real $x \neq 0$ and $\operatorname{sinc}(0) = 1$,
and let $f \colon \mathbb{R} \to \mathbb{C}$ be a Schwartz function whose Fourier transform
$\hat f(\xi) = \int_{\mathbb{R}} f(x)\, e^{-2\pi i x \xi}\, dx$ vanishes at every real $\xi$
outside $[-\frac12, \frac12]$. Then for every real $t$ the series
$\sum_{n \in \mathbb{Z}} f(n) \operatorname{sinc}(\pi(n - t))$ is summable over $\mathbb{Z}$
(unconditionally convergent) and

$$
f(t) = \sum_{n \in \mathbb{Z}} f(n) \operatorname{sinc}(\pi(n - t)).
$$

This is Shannon's Theorem 1 and the interpolation series (7), with band $W = \tfrac12$ and samples $1/(2W) = 1$ apart.

Proof: on $(-\tfrac12, \tfrac12)$ the spectrum is [the Fourier series of the samples](fourier-eq-tsum.md); Fourier inversion writes $f(t) = \int_{-1/2}^{1/2} \hat f(\xi)\, e^{2\pi i t \xi}\,d\xi$; the series converges uniformly because $\sum_n |f(n)| < \infty$, so it can be integrated term by term, and $\int_{-1/2}^{1/2} e^{2\pi i (t - n)\xi}\,d\xi = \operatorname{sinc}(\pi(n - t))$.

## Sources

- C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949), 10–21, Theorem 1 and the interpolation series (7); H. Nyquist (1928); E. T. Whittaker (1915). Knill, *Some fundamental theorems in mathematics*, §179. Problem `nyquist_shannon_sampling` of the lean-eval benchmark.
