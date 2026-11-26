# Poisson conditioning, two cells

Let $X, Y$ be independent measurable $\mathbb{N}$-valued random variables on a measure space
$(\Omega, \mu)$ with $X \sim \operatorname{Poisson}(a)$ and $Y \sim \operatorname{Poisson}(b)$, where
$a, b \ge 0$ and $a + b > 0$. Then for all $N, k \in \mathbb{N}$,

$$\mu\bigl(X = k \bigm| X + Y = N\bigr) = \operatorname{Bin}\Bigl(N, \frac{a}{a + b}\Bigr)(\{k\}),$$

that is, $\binom{N}{k} \bigl(\frac{a}{a+b}\bigr)^k \bigl(\frac{b}{a+b}\bigr)^{N - k}$ for $k \le N$ and $0$
for $k > N$.

## Sources

- N. L. Johnson, S. Kotz and N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997, Chapter 35.
