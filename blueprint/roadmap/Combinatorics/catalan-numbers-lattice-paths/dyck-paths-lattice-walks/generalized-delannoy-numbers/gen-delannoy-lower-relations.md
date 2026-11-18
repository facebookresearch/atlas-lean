# Relationship identities for generalized Delannoy numbers

For natural numbers $k$, $m$, $n$ with $k \ge 1$, $m \ge k$ and $n \ge k$, the
[lower generalized Delannoy numbers](gen-delannoy-lower.md) satisfy

$$\begin{aligned}
D_k(m, n) + D_k(m, n + 1) &= 2 D_{k-1}(m, n), &\qquad D_k(m, n) + D_k(m + 1, n) &= D_{k+1}(m + 1, n + 1),\\
D_k(m, n + 1) - D_k(m, n) &= 2 D_{k-1}(m - 1, n), &\qquad D_k(m + 1, n) - D_k(m, n) &= D_{k+1}(m + 1, n).
\end{aligned}$$

In the fourth identity with $n = k$, the number $D_{k+1}(m + 1, k)$ is $0$, which is what the source formula gives with $\binom{a}{-1} = 0$: every binomial coefficient in its defining sum has lower index $n - (k + 1) = -1$. The identity then reads $D_k(m + 1, k) = D_k(m, k)$, both sides being $2^k$. If the lower index $-1$ were replaced by $0$, as truncated subtraction would do, $D_{k+1}(m + 1, k)$ would be $2^k$ and the identity would fail; for example, at $k = m = n = 1$ the left side is $D_1(2, 1) - D_1(1, 1) = 2 - 2 = 0$.

## Sources

- Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal of Integer Sequences 27 (2024), Article 24.1.8, Theorem 7 (`jis-2024-24.1.8-thm-7`).
