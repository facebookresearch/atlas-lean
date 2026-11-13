# Binet formula for the $r$-Lucas polynomials (one double zero)

Let $K$ be a field of
characteristic zero, let $r \ge 1$ and $s$ be natural numbers, and let $x, y, \alpha \in K$ with
$\alpha \ne 0$. Suppose that $t^{r+1} - x t^r - y = (t - \alpha)^2 \tilde P(t)$ in $K[t]$, where
$\tilde P(t) = \prod_{k=1}^{r-1} (t - \beta_k)$ for pairwise distinct
$\beta_1, \dots, \beta_{r-1} \in K$, all different from $\alpha$. Then for every $n \ge 0$ the
$r$-Lucas polynomials of type $s$ satisfy

$$V^{(r,s)}_n(x, y) = \frac{\alpha^{n+r-1}}{\tilde P(\alpha)} \left( n \, \frac{r-s}{r} + r +
\frac{s}{r} - \alpha \, \frac{r-s}{r} \, \frac{\tilde P'(\alpha)}{\tilde P(\alpha)} \right) +
\sum_{k=1}^{r-1} \frac{\beta_k^n ((s+1) \beta_k - s x)}{(r+1) \beta_k - r x}.$$

The paper's hypothesis $y = -\frac{1}{r} \left( \frac{rx}{r+1} \right)^{r+1}$ (which makes
$\alpha = rx/(r+1)$ the double zero) is replaced by the factorization it yields. The paper takes
$1 \le s \le r$; the identity holds for every $s$. The hypothesis $\alpha \ne 0$ is added: for
$r = 2$, $y = 0$ the factorization $t^2 (t - x)$ has $\alpha = 0$ and the formula fails at $n = 0$
(for $x = s = 1$: $V_0 = 2$, right side $1$). In the paper's setting $\alpha = rx/(r+1)$ with
$x \ne 0$, so $\alpha \ne 0$; the only other $\alpha = 0$ case, $r = 1$, $x = y = 0$, is dropped.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Theorem 1.
