# Digamma series for the signed stride sum

Let $q \ge 1$ and $t \ge 1$ be integers, let
$a$ be a real number with $-1 \le a < 1$, let $T_{q,t}$ denote the signed stride sum and $\psi$
the digamma function. As $N \to \infty$, the partial sums

$$
\sum_{n=1}^{N} (-1)^{n+1} \frac{2n + q}{(n + a + 1)(n - a - 1 + q)} \, T_{q,t}(n)
$$

converge to

$$
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^t}
\left[\psi\left(\frac{n+a+1+q}{2q}\right) - \psi\left(\frac{n+a+1}{2q}\right)\right] +
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^t}
\left[\psi\left(\frac{n-a-1+2q}{2q}\right) - \psi\left(\frac{n-a-1+q}{2q}\right)\right].
$$

The first series converges only conditionally, while the two digamma series converge
absolutely.

## Sources

- Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2, equation (24).
