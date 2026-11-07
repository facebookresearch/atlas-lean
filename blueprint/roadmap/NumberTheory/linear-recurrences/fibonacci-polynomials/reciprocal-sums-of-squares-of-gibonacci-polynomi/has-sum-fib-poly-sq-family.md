# Series over a family of Fibonacci polynomial squares

Let $x > 0$ be real, let
$\alpha = (x + \sqrt{x^2 + 4})/2$, and let $f_n = f_n(x)$ be the Fibonacci polynomials, given by
$f_0 = 0$, $f_1 = 1$ and $f_{n+2} = x f_{n+1} + f_n$, evaluated at $x$. Let $k$, $r$, $t$ be
positive integers and $p$ a natural number with $t \le 2p$. Then the series

$$\sum_{n=1}^{\infty} \frac{(-1)^{tk} f_r f_{2pk}}{f_{(2pn+t-p)k}^2 - (-1)^{tk} f_{pk}^2}$$

converges unconditionally, and its sum is $f_{tk+r} / f_{tk} - \alpha^r$.

This is the Fibonacci-polynomial case of Theorem 3.1 of the source. The source takes $x$ to be an
integer; the statement is made for real $x > 0$, which contains the positive integers.

## Sources

- Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares: Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Theorem 3.1.
