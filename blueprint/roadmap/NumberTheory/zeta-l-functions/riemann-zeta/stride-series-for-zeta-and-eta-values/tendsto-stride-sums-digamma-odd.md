# Digamma identity for stride sums over odd indices

Let $q, t \ge 1$ be integers, let
$a$ be a real number with $-1 \le a < 1$, let $S_{q,t}(n)$ denote the alternating stride sum and
$T_{q,t}(n)$ the signed stride sum, and let $\psi$ be the digamma function. Then the partial sums

$$\sum_{n=1}^{N} \frac{2n+q}{2(n+a+1)(n-a-1+q)} \bigl(S_{q,t}(n) + (-1)^{n+1} T_{q,t}(n)\bigr)$$

converge, as $N \to \infty$, to

$$\frac{1}{2q} \sum_{n \ge 1} \frac{1}{(2n-1)^t}
\Bigl[\psi\Bigl(\frac{2n+a+q}{2q}\Bigr) - \psi\Bigl(\frac{2n+a}{2q}\Bigr)\Bigr] +
\frac{1}{2q} \sum_{n \ge 1} \frac{1}{(2n-1)^t}
\Bigl[\psi\Bigl(\frac{2n-a-2+2q}{2q}\Bigr) - \psi\Bigl(\frac{2n-a-2+q}{2q}\Bigr)\Bigr].$$

Deviation: the paper prints the factor $2$ where this statement has $1/2$; as printed the
series sums to four times this limit (for $q = t = 1$ and $a = -1$: $4\lambda(2) \approx 4.935$
against $\lambda(2) = \pi^2/8 \approx 1.234$, where $\lambda(s) = \sum_{n \ge 0} (2n+1)^{-s}$
is the Dirichlet lambda function). With $1/2$ the identity checks numerically for several
$(a, q, t)$, and at $a = -1$ it is the stride series for $\lambda(t+1)$, half the sum of the
paper's series (9) for $\zeta(t+1)$ and (25) for $\eta(t+1)$.

## Sources

- Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 3, equation (27) (`integers-2024-A45-thm-3`).
