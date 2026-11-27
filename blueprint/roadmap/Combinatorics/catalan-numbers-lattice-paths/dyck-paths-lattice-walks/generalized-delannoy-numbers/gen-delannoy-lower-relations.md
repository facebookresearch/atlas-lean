# Relationship identities for generalized Delannoy numbers

For natural numbers $k$, $m$, $n$ with $k \ge 1$, $m \ge k$ and $n \ge k$, the
[lower generalized Delannoy numbers](gen-delannoy-lower.md) satisfy

$$\begin{aligned}
D_k(m, n) + D_k(m, n + 1) &= 2 D_{k-1}(m, n), &\qquad D_k(m, n) + D_k(m + 1, n) &= D_{k+1}(m + 1, n + 1),\\
D_k(m, n + 1) - D_k(m, n) &= 2 D_{k-1}(m - 1, n),
\end{aligned}$$

and, if moreover $k < n$,

$$D_k(m + 1, n) - D_k(m, n) = D_{k+1}(m + 1, n).$$

The condition $k < n$ keeps the right-hand side of the fourth identity in the domain $n \ge k + 1$ of $D_{k+1}$. At $n = k$, every binomial coefficient in the defining sum of $D_{k+1}(m + 1, k)$ has lower index $n - (k + 1) = -1$: the source's convention $\binom{a}{-1} = 0$ makes that number $0$, and the identity then reads $D_k(m + 1, k) = D_k(m, k)$, both sides being $2^k$. If the lower index $-1$ is replaced by $0$, as truncated subtraction does, the number is $2^k$ and the identity fails; for example, at $k = m = n = 1$ the left side is $D_1(2, 1) - D_1(1, 1) = 2 - 2 = 0$.

## Sources

- Steven Edwards and William Griffiths, *Delannoy Constructions*, Journal of Integer Sequences 27 (2024), Article 24.1.8, Theorem 7 (`jis-2024-24.1.8-thm-7`).
