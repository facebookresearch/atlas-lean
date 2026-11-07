# Reciprocal sums of shifted squares of Fibonacci and Lucas polynomials (Koshy–Gao, Theorem 2.1)

**Reciprocal sums of shifted squares of Fibonacci and Lucas polynomials (Koshy–Gao,
Theorem 2.1).** Let $f_n(x)$ and $l_n(x)$ be the Fibonacci and Lucas polynomials, given by
$z_{n+2} = x z_{n+1} + z_n$ with initial values $f_0 = 0$, $f_1 = 1$ and $l_0 = 2$, $l_1 = x$.
Let $x > 0$ be real, let $k$, $p$, $r$, $t$ be positive integers with $t \le 2p$, and let
$\alpha = (x + \sqrt{x^2 + 4})/2$. Then

$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk} f_r(x) f_{2pk}(x)}
{f_{(2pn+p+t)k}(x)^2 - (-1)^{tk} f_{pk}(x)^2} =
\frac{f_{tk+r}(x)}{f_{tk}(x)} - \alpha^r
$$

and

$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk+1} (x^2 + 4) f_r(x) f_{2pk}(x)}
{l_{(2pn+p+t)k}(x)^2 + (-1)^{tk} (x^2 + 4) f_{pk}(x)^2} =
\frac{l_{tk+r}(x)}{l_{tk}(x)} - \alpha^r.
$$

In the source the sums run over $n \ge 1$, with $(2pn + t - p)k$ in place of $(2pn + p + t)k$;
here the summation index is shifted to start at $n = 0$.

## Sources

- Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023, Theorem 2.1 (`fq-2024-koshy12202023-thm-2.1`).
