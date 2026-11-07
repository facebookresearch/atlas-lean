# Reciprocal sums of shifted squares of Jacobsthal and Jacobsthal–Lucas polynomials (Koshy–Gao, Theorem 3.1)

**Reciprocal sums of shifted squares of Jacobsthal and Jacobsthal–Lucas polynomials
(Koshy–Gao, Theorem 3.1).** Let $J_n(x)$ and $j_n(x)$ be the Jacobsthal and Jacobsthal–Lucas
polynomials, given by $z_{n+2} = z_{n+1} + x z_n$ with initial values $J_0 = 0$, $J_1 = 1$ and
$j_0 = 2$, $j_1 = 1$. Let $x > 0$ be real, let $k$, $p$, $r$, $t$ be positive integers with
$t \le 2p$, let $w = (1 + \sqrt{4x + 1})/2$, and write $e_n = (2pn + t)k$. Then

$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk} x^{e_n} J_r(x) J_{2pk}(x)}
{J_{(2pn+p+t)k}(x)^2 - (-1)^{tk} x^{e_n} J_{pk}(x)^2} =
\frac{J_{tk+r}(x)}{J_{tk}(x)} - w^r
$$

and

$$
\sum_{n=0}^{\infty} \frac{(-1)^{tk+1} (4x + 1) x^{e_n} J_r(x) J_{2pk}(x)}
{j_{(2pn+p+t)k}(x)^2 + (-1)^{tk} (4x + 1) x^{e_n} J_{pk}(x)^2} =
\frac{j_{tk+r}(x)}{j_{tk}(x)} - w^r.
$$

In the source the sums run over $n \ge 1$, with $(2pn + t - p)k$ in place of $(2pn + p + t)k$
and exponent $(2pn + t - 2p)k$ in place of $e_n$; here the summation index is shifted to start
at $n = 0$.

## Sources

- Thomas Koshy and Zhenguang Gao, *Sums Involving a Family of Jacobsthal Polynomial Squares*, The Fibonacci Quarterly 62 (2024), Article koshy12202023, Theorem 3.1 (`fq-2024-koshy12202023-thm-3.1`).
