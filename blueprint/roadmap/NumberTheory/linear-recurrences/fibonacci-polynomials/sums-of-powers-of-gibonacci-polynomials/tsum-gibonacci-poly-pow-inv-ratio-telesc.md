# Telescoping sum of powers of inverse gibonacci polynomial ratios

Let $f_n$ and $l_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$, $l_1 = x$
and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number $x > 0$, and
let $\beta = (x - \sqrt{x^2 + 4})/2$. Then for $g \in \{f, l\}$, every positive integer $k$ and
all natural numbers $r$ and $\lambda$,

$$\sum_{n \ge 0} \left(\frac{g_{(2n+1)k}^\lambda}{g_{(2n+1)k+r}^\lambda} -
\frac{g_{(2n+3)k}^\lambda}{g_{(2n+3)k+r}^\lambda}\right)
= \frac{g_k^\lambda}{g_{k+r}^\lambda} - (-\beta)^{r\lambda}.$$

## Sources

- Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*, The Fibonacci Quarterly 62 (2024), Article koshy07202023, Lemma 2.2.
