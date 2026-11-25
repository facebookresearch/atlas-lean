# Denominators of higher derivatives of Bernoulli polynomials

For $m \ge 0$ let
$\mathfrak{D}_m$ be the denominator of the Bernoulli polynomial $B_m(x)$, and for $k \ge 1$ let
$\mathfrak{D}_n^{(k)}$ be the denominator of the $k$-th derivative $B_n^{(k)}(x)$ of $B_n(x)$.
Write $(n)_k = n(n-1)\cdots(n-k+1)$ for the falling factorial, $s_p(m)$ for the sum of the
base-$p$ digits of $m$, $\operatorname{rad}(n)$ for the product of the primes dividing $n$, and
$\mathbb{D}^{\perp}_m$ for the product of the primes $p \nmid m$ with $s_p(m) \ge p$. Let
$k, n \ge 1$. If $k \le n$, then

$$\mathfrak{D}_n^{(k)} = \frac{\mathfrak{D}_{n-k}}{\gcd(\mathfrak{D}_{n-k}, (n)_k)}
= \frac{\mathbb{D}^{\perp}_{n-k+1}}{\gcd(\mathbb{D}^{\perp}_{n-k+1}, (n)_{k-1})}
= \prod_{p \text{ prime},\ p \le n,\ p \nmid (n)_k,\ s_p(n-k+1) \ge p} p.$$

If $n < k$, then $\mathfrak{D}_n^{(k)} = 1$. No prime $p \le k$ divides $\mathfrak{D}_n^{(k)}$.
Finally, $\mathfrak{D}_n^{(1)} = \mathfrak{D}_{n-1} / \operatorname{rad}(n) = \mathbb{D}^{\perp}_n$.

## Sources

- Bernd C. Kellner, *On the Finiteness of Bernoulli Polynomials Whose Derivative Has Only Integral Coefficients*, Journal of Integer Sequences 27 (2024), Article 24.2.8, Theorem 13 (`jis-2024-24.2.8-thm-13`).
