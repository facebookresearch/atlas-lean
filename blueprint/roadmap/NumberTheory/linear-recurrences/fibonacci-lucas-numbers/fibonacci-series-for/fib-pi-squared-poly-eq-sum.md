# Explicit formula for the polynomials $p_n$

Let $p_1, p_2, \dots$ be polynomials with
integer coefficients such that $p_1 = 1$ and, for every $n \ge 1$,
$p_{n+1}(x) = (2x + 2n + 1)(2x + 2n + 2)\, p_n(x) - (x + 1)^2 p_n(x + 1)$. Then for every
$n \ge 1$, as polynomials in $x$,

$$p_n(x) = \sum_{j=0}^{n-1} (-1)^j \binom{n-1}{j} \Bigl(\prod_{k=2j+3}^{2n} (2x + k)\Bigr)
\prod_{t=1}^{j} (x + t)^2.$$

## Sources

- Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1, Lemma 2.4.
