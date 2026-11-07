# A weighted sum of the corrected Genocchi–Lucas coefficients

Let $G_k$ be the Genocchi
numbers and $L_n$ the Lucas numbers, and for each natural number $n$ let

$$c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2\sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}.$$

For every natural number $m$,

$$\sum_{n=0}^{m} \left(\frac{2}{\sqrt{5}}\right)^{n} \binom{m}{n} c_n =
\frac{2\sqrt{5}}{\sqrt{5}^{\,m}}.$$

Expanding $c_n$ splits the left side into the paper's printed double sum
$\sum_{n,k} 2^n \sqrt{5}^{\,k-n} \binom{n}{k} \binom{m}{n} G_k \frac{L_{n-k+1}}{n-k+1}$ and a
correction term; the printed double sum alone gives the right side only for odd $m$ (at $m = 2$
it is $12\sqrt{5}/5$, not $2\sqrt{5}/5$).

## Sources

- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Corollary 13.
