# Telescoping inverse-power series of gibonacci polynomials at even indices, even shift

Let $x > 0$ be real, and let $g_n$ denote either the Fibonacci polynomials, given by $g_0 = 0$ and
$g_1 = 1$, or the Lucas polynomials, given by $g_0 = 2$ and $g_1 = x$, both satisfying
$g_{n+2} = x g_{n+1} + g_n$ and evaluated at $x$. Let $k$ be an even natural number and
$\lambda$ a positive integer. Then

$$\sum_{n=0}^{\infty} \left(\frac{1}{g_{2n+2}^{\lambda}} - \frac{1}{g_{2n+2+2k}^{\lambda}}\right) =
\sum_{r=1}^{k} \frac{1}{g_{2r}^{\lambda}}.$$

The source quotes this lemma from Koshy as the sum over $n \ge k/2 + 1$ of
$1/g_{2n-k}^{\lambda} - 1/g_{2n+k}^{\lambda}$; here the summation index is shifted to start at $0$.

## Sources

- Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article linzhou02172024, Lemma 2.3 (`fq-2024-linzhou02172024-lem-2.3`).
