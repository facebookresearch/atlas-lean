# The Mertens remainder from a Chebyshev bound

Let $k \ge 1$ be an integer and let
$\eta > 0$ and $x_0 > 1$ be reals such that $|\vartheta(y) - y| < \eta y / \log^k y$ for every
real $y \ge x_0$, where $\vartheta(y) = \sum_{p \le y} \log p$ is Chebyshev's function. For
real $x$ let $S(x) = \sum_{p > x} \big(\log(1 - 1/p) + 1/p\big)$, the sum over the primes
$p > x$. Then for every real $x \ge x_0$,

$$
\Big|S(x) - \sum_{m \ge 1} \frac{\operatorname{li}(x^{-m})}{m+1}\Big| <
\frac{\eta}{\log^{k+1} x} \Big((x+1) \log\frac{x}{x-1} - 1\Big),
$$

where $\operatorname{li}$ is the logarithmic integral.

## Sources

- Christian Axler, *Effective Estimates for Some Functions Defined over Primes*, INTEGERS 24 (2024), Article A34, Proposition 8 (`integers-2024-A34-prop-8`); `S(x)` as in the paper's equation (6.5).
