# Explicit asymptotic for the logarithmic mean of the divisor function

Let $\tau(n)$ be
the number of positive divisors of $n$ and let $\gamma$ be the Euler–Mascheroni constant. There
is a real constant $C$ such that $\sum_{k=1}^{N} \frac{\log k}{k} - \frac{(\log N)^2}{2}$ tends
to $\frac{\gamma^2 - C}{2}$ as $N \to \infty$ and such that for every real $x \ge 2$,
$\left|\sum_{1 \le n \le x} \frac{\tau(n)}{n} -
\left(\frac{(\log x)^2}{2} + 2\gamma \log x + C\right)\right| \le \frac{2.1 \log x}{x^{2/3}}$.

The first condition says that $C = \gamma^2 - 2\gamma_1$, where
$\gamma_1 = \lim_{N \to \infty} \left(\sum_{k=1}^{N} \frac{\log k}{k} - \frac{(\log N)^2}{2}\right)$
is the first Stieltjes constant.

## Sources

- Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25 (2025), Article A48, Lemma 7.1 (`integers-2025-A48-lem-7-1`).
