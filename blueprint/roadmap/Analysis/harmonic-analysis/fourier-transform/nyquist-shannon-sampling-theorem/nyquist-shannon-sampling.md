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

## Sources

- C. E. Shannon, *Communication in the presence of noise*, Proc. IRE 37 (1949); H. Nyquist (1928); E. T. Whittaker (1915). Knill, *Some fundamental theorems in mathematics*, §179. Problem `nyquist_shannon_sampling` of the lean-eval benchmark.
