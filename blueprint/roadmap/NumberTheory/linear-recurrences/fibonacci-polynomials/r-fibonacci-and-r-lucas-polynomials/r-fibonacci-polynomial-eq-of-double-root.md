# Binet formula for the r-Fibonacci polynomials with one double zero

Let $K$ be a field
of characteristic zero, let $r \ge 1$ be a natural number, and let $x, y, \alpha \in K$. Let
$\beta_1, \dots, \beta_{r-1} \in K$ be pairwise distinct and all different from $\alpha$, put
$\tilde P(t) = \prod_{k=1}^{r-1} (t - \beta_k)$, and suppose that
$t^{r+1} - x t^r - y = (t - \alpha)^2 \tilde P(t)$ as polynomials over $K$. Then for every
natural number $n$ the $r$-Fibonacci polynomial $U^{(r)}$ satisfies

$$
U^{(r)}_{n+1}(x, y) = \frac{\alpha^{n+r-1}}{\tilde P(\alpha)}
\Bigl((n + r) - \frac{\alpha \tilde P'(\alpha)}{\tilde P(\alpha)}\Bigr) +
\sum_{k=1}^{r-1} \frac{\beta_k^{n+1}}{(r+1)\beta_k - r x}.
$$

The paper's hypothesis $y = -\frac{1}{r}\bigl(\frac{rx}{r+1}\bigr)^{r+1}$ (which makes
$\alpha = rx/(r+1)$ the double zero) is replaced by the factorization it yields.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Theorem 1 (`integers-2025-A38-thm-1`).
