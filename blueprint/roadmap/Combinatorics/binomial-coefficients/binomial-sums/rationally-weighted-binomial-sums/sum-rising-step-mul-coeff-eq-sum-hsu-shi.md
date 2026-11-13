# Scherk's identity with $s$-rising factorials

Let $s$ be a real number and let $S(n, k)$
be the generalized Stirling numbers of Hsu and Shiue with parameters $(-s, 1, 0)$: a real array
with $S(0, 0) = 1$, $S(n, 0) = 0$ for $n \ge 1$, $S(n, k) = 0$ for $n < k$, and
$S(n+1, k+1) = S(n, k) + (k + 1 + ns) \, S(n, k+1)$ for all $n, k \ge 0$. Let $N$ and $r$ be
natural numbers, let $a_0, \dots, a_N$ be real numbers, and let $f(y) = \sum_{k=0}^{N} a_k y^k$,
with $i$-th derivative $f^{(i)}$. Then for every real number $x > 0$,

$$\sum_{k=0}^{N} k (k + s) \cdots (k + (r-1)s) \, a_k x^{k + rs} =
\sum_{i=0}^{r} S(r, i) \, x^{rs + i} f^{(i)}(x),$$

where the product $k (k + s) \cdots (k + (r-1)s)$ has the $r$ factors $k + js$, $0 \le j < r$,
and is $1$ when $r = 0$.

The powers of $x$ have real exponents, which is why $x > 0$ is assumed.

## Sources

- Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.1, equation (2.2).
