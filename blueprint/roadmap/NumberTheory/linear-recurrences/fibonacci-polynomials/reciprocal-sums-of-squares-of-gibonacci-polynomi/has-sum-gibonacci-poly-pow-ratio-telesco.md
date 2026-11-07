# A telescoping series of powers of gibonacci polynomial ratios

Let $x > 0$ be real, let
$\alpha = (x + \sqrt{x^2 + 4})/2$, and let $g_n$ be either the Fibonacci polynomials $f_n(x)$,
given by $f_0 = 0$ and $f_1 = 1$, or the Lucas polynomials $l_n(x)$, given by $l_0 = 2$ and
$l_1 = x$, where both satisfy $z_{n+2} = x z_{n+1} + z_n$. Let $k$, $r$, $t$, $\lambda$ be positive
integers and $p$ a natural number with $t \le 2p$. Then the series

$$\sum_{n=1}^{\infty} \left[ \left( \frac{g_{(2pn+t-2p)k+r}}{g_{(2pn+t-2p)k}} \right)^{\lambda} -
\left( \frac{g_{(2pn+t)k+r}}{g_{(2pn+t)k}} \right)^{\lambda} \right]$$

converges unconditionally, and its sum is
$\left( g_{tk+r} / g_{tk} \right)^{\lambda} - \alpha^{\lambda r}$.

The source takes $x$ to be an integer; the statement is made for real $x > 0$, which contains the
positive integers.

## Sources

- Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares: Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Lemma 2.1 (`fq-2024-koshy11112023-lem-2.1`).
