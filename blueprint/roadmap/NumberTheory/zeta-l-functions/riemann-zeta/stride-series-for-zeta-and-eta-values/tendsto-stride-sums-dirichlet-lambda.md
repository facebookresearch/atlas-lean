# Stride series for the Dirichlet lambda function

Let $q, t \ge 1$ be integers, and let
$S_{q,t}(n)$ denote the alternating stride sum and $T_{q,t}(n)$ the signed stride sum. Then the
partial sums

$$\sum_{n=1}^{N} \frac{2n+q}{2n(n+q)} \bigl(S_{q,t}(n) + (-1)^{n+1} T_{q,t}(n)\bigr)$$

converge, as $N \to \infty$, to $\lambda(t+1)$, where $\lambda(s) = \sum_{n \ge 0} (2n+1)^{-s}$ is
the Dirichlet lambda function. The series is half the sum of the paper's series (9) for
$\zeta(t+1)$ and (25) for $\eta(t+1)$.

Deviation: the paper prints the factor $2$ where this statement has $1/2$; as printed the
series sums to $4\lambda(t+1)$ (for $q = t = 1$: about $4.935$ against
$\lambda(2) = \pi^2/8 \approx 1.234$).

## Sources

- Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 3, equation (28) (`integers-2024-A45-thm-3`).
