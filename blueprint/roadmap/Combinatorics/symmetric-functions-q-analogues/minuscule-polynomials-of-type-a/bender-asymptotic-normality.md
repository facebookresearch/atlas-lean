# Bender's central limit theorem for polynomials with non-positive real zeros

For each
natural number $n$ let $r_{n,0}, \dots, r_{n,n-1}$ be non-negative real numbers, and let $a(n,k)$
be the coefficient of $x^k$ in the real polynomial $A_n(x) = \prod_{i\lt n} (x + r_{n,i})$. Put
$\mu_n = \sum_{i\lt n} 1/(1 + r_{n,i})$ and $\sigma_n^2 = \sum_{i\lt n} r_{n,i}/(1 + r_{n,i})^2$, and let
$\sigma_n \ge 0$ be the square root of $\sigma_n^2$. Then for every $n$,
$\sum_{k=0}^{n} k\, a(n,k) / \sum_{k=0}^{n} a(n,k) = \mu_n$ and
$\sum_{k=0}^{n} (k - \mu_n)^2 a(n,k) / \sum_{k=0}^{n} a(n,k) = \sigma_n^2$. Moreover, if
$\sigma_n^2 \to \infty$ as $n \to \infty$, then for every real $x$,
$\sum_{0 \le k \le n,\ k \le \mu_n + x \sigma_n} a(n,k) / \sum_{k=0}^{n} a(n,k)$ tends to $\Phi(x)$
as $n \to \infty$, where $\Phi$ is the distribution function of the standard normal distribution.

## Sources

- Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of Integer Sequences 28 (2025), Article 25.1.2, Lemma 12 (Bender, Theorem 2).
