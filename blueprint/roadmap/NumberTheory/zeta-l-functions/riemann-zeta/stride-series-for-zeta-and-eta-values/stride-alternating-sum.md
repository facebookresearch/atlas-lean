# Alternating stride sum

For natural numbers $q$, $t$ and $n$, let
$K = \lfloor (n + q - 1)/q \rfloor$ if $q \ge 1$ and $K = 0$ if $q = 0$. The alternating stride
sum is the real number

$$
S_{q,t}(n) = \sum_{i=0}^{K-1} \frac{(-1)^i}{(n - qi)^t}.
$$

For $q \ge 1$ this is the alternating sum of $m^{-t}$ over $m = n, n - q, n - 2q, \dots$ with
$m \ge 1$; with $j = i + 1$ it reads $\sum_{j=1}^{K} (-1)^{j+1}/(n + q - qj)^t$.

## Sources

- Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1, equation (9).
