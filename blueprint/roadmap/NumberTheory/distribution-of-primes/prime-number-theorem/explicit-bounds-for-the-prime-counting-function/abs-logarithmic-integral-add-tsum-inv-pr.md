# Tails of prime power sums from a Chebyshev bound

Let $k \ge 1$ be an integer and let
$\eta > 0$ and $x_0 > 1$ be reals such that $|\vartheta(y) - y| < \eta y / \log^k y$ for every
real $y \ge x_0$, where $\vartheta(y) = \sum_{p \le y} \log p$ is Chebyshev's function. Then
for every integer $n \ge 2$ and every real $x \ge x_0$,

$$
\Big|\operatorname{li}(x^{1-n}) + \sum_{p > x} \frac{1}{p^n}\Big| <
\frac{\eta}{x^{n-1} \log^{k+1} x} \Big(1 + \frac{n}{n-1}\Big),
$$

where $\operatorname{li}$ is the logarithmic integral and the sums run over primes $p$.

## Sources

- Christian Axler, *Effective Estimates for Some Functions Defined over Primes*, INTEGERS 24 (2024), Article A34, Lemma 6 (`integers-2024-A34-lem-6`).
