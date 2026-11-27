# Klamkin's Gauss summation

Let $n \ge 1$ be an integer and let $a$ and $b$ be real numbers
such that $-a$ and $-b$ are not nonnegative integers, $a + 1 + n < 0$, and $a - b + 1$ is not a
nonnegative integer. Then

$$
{}_2F_1(n, b + 1; b - a; 1) =
  \frac{\Gamma(-a - n - 1)\,\Gamma(b - a)}{\Gamma(b - a - n)\,\Gamma(-a - 1)},
$$

where ${}_2F_1(\alpha, \beta; \gamma; 1) =
\sum_{k \ge 0} \frac{(\alpha)_k (\beta)_k}{(\gamma)_k\, k!}$ and $(x)_k$ is the rising factorial.

The condition $a + 1 + n < 0$ makes the series converge. The Gamma function is taken to be $0$
at its poles and division by $0$ gives $0$, so the right side is $0$ when $b - a - n$ is a
nonpositive integer.

## Sources

- U. Abel, "A Short Proof of the Binomial Identities of Frisch and Klamkin," _Journal of Integer Sequences_ 23 (2020), Article 20.7.1.
