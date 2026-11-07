# Gibonacci polynomial square sums at even multiples of the index

Let $f_n$ and $l_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$, $l_1 = x$
and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number $x > 0$, and
let $\alpha = (x + \sqrt{x^2 + 4})/2$. Let $g$ be $f$ with $(\mu, \nu) = (1, -1)$, or $l$ with
$(\mu, \nu) = (x^2 + 4, 1)$. Then for every positive integer $k$ and every natural number $r$,

$$\sum_{n \ge 1} \frac{(-1)^{k+1} \mu \nu f_r f_{2k}}{g_{2nk}^2 + (-1)^k \mu \nu f_k^2}
= \frac{g_{k+r}}{g_k} - \alpha^r.$$

The extracted statement of this theorem prints the numerator with $(-1)^k$ in place of
$(-1)^{k+1}$, which negates the left side and makes the identity false (for $x = 1$, $g = f$ and
$k = r = 1$ that left side is $(\sqrt{5} - 1)/2$ while the right side is $(1 - \sqrt{5})/2$); the
paper's proof and its corollaries use the sign stated here.

## Sources

- Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*, The Fibonacci Quarterly 62 (2024), Article koshy07202023, Theorem 3.1.
