# Series over a family of Lucas polynomial squares

Let $x > 0$ be real, let
$\Delta = \sqrt{x^2 + 4}$ and $\alpha = (x + \Delta)/2$, and let $f_n$ and $l_n$ be the
Fibonacci and Lucas polynomials evaluated at $x$, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$,
$l_1 = x$ and the recurrence $z_{n+2} = x z_{n+1} + z_n$ for both. Let $k$, $r$, $t$ be positive
integers and $p$ a natural number with $t \le 2p$. Then the series

$$\sum_{n=1}^{\infty} \frac{-(-1)^{tk} \Delta^2 f_r f_{2pk}}
{l_{(2pn+t-p)k}^2 + (-1)^{tk} \Delta^2 f_{pk}^2}$$

converges unconditionally, and its sum is $l_{tk+r} / l_{tk} - \alpha^r$.

This is the Lucas-polynomial case of Theorem 3.1 of the source. The source takes $x$ to be an
integer; the statement is made for real $x > 0$, which contains the positive integers.

## Sources

- Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares: Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Theorem 3.1.
