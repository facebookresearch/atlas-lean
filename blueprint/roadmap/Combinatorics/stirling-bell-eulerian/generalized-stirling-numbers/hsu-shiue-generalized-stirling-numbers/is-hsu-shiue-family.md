# Characterization of the Hsu–Shiue generalized Stirling numbers

Let $K$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $\alpha, \beta, r \in K$. For $z \in K$ write $(z \mid \alpha)_0 = 1$ and
$(z \mid \alpha)_n = z (z - \alpha) \cdots (z - (n-1)\alpha)$ for $n \ge 1$ (the generalized
falling factorial). An array $(S(n,k))_{n, k \ge 0}$ in $K$ is a Hsu–Shiue family with
parameters $(\alpha, \beta, r)$ when $\alpha$, $\beta$ and $r$ are not all zero,
$S(n, 0) = (r \mid \alpha)_n$ for every $n \ge 0$, $S(n, k) = 0$ whenever $n < k$, and

$$S(n+1, k+1) = S(n, k) + \bigl((k+1)\beta - n\alpha + r\bigr) S(n, k+1)$$

for all $n, k \ge 0$.

The last condition is the source recurrence
$S(n+1, k) = S(n, k-1) + (k\beta - n\alpha + r) S(n, k)$ at the indices $k \ge 1$; the initial
column and the triangular support fix the remaining values.
