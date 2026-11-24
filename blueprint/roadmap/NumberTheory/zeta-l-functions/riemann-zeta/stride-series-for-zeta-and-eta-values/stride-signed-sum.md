# Signed stride sum

For natural numbers $q$, $t$ and $n$, let
$K = \lfloor (n + q - 1)/q \rfloor$ if $q \ge 1$ and $K = 0$ if $q = 0$. The signed stride sum is
the real number

$$
T_{q,t}(n) = \sum_{i=0}^{K-1} \frac{(-1)^{(q+1)i}}{(n - qi)^t}.
$$

With $j = i + 1$ it reads $\sum_{j=1}^{K} (-1)^{(q+1)(j+1)}/(n + q - qj)^t$. For odd $q$ every
sign is $+$, and for even $q$ the signs alternate.

## Sources

- Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2, equation (25).
