# Digamma series for the alternating stride sum

Let $q \ge 1$ and $t \ge 1$ be integers,
let $S_{q,t}$ denote the alternating stride sum and $\psi$ the digamma function. As
$N \to \infty$, the partial sums

$$
\sum_{n=1}^{N} \frac{2n + q}{(n + \frac12)(n - \frac12 + q)} \, S_{q,t}(n)
$$

converge to

$$
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{1}{n^t}
\left[\psi\left(\frac{n+\frac12+q}{2q}\right) - \psi\left(\frac{n+\frac12}{2q}\right)\right] +
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{1}{n^t}
\left[\psi\left(\frac{n-\frac12+2q}{2q}\right) - \psi\left(\frac{n-\frac12+q}{2q}\right)\right].
$$

## Sources

- Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1, equation (20).
