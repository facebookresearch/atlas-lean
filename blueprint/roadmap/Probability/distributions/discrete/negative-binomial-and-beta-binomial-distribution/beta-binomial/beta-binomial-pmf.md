# Beta-binomial mass function

For $n \in \mathbb{N}$, real $\alpha, \beta$ and $k \in \mathbb{N}$, the beta-binomial mass function is

$$\mathrm{BB}(n; \alpha, \beta)(k) = \frac{\binom{n}{k} \alpha^{(k)} \beta^{(n - k)}}{(\alpha + \beta)^{(n)}},$$

with the rising factorial $x^{(k)} = x(x+1)\cdots(x+k-1)$, $n - k$ truncated at $0$, and a quotient
with zero denominator read as $0$. It vanishes for $k > n$ (since $\binom{n}{k} = 0$), and it is a
probability mass function on $\{0, \dots, n\}$ for $\alpha, \beta > 0$.

## Sources

- N. L. Johnson, A. W. Kemp and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley, 2005, Chapter 6.
