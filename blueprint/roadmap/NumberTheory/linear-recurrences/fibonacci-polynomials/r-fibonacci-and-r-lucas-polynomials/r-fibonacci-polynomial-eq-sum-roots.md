# Binet formula for the $r$-Fibonacci polynomials (distinct zeros)

Let $K$ be a field, let
$r \ge 1$ be a natural number and let $x, y \in K$. Suppose that
$t^{r+1} - x t^r - y = \prod_{k=0}^{r} (t - \alpha_k)$ in $K[t]$, where
$\alpha_0, \dots, \alpha_r \in K$ are pairwise distinct. Then for every $n \ge 0$ the
$r$-Fibonacci polynomials $U^{(r)}_n(x, y)$ satisfy

$$U^{(r)}_{n+1}(x, y) = \sum_{k=0}^{r} \frac{\alpha_k^{n+1}}{(r+1) \alpha_k - r x}.$$

The paper's hypothesis $y \ne -\frac{1}{r} \left( \frac{rx}{r+1} \right)^{r+1}$ is replaced by the
distinctness of the zeros it is meant to guarantee (it does not exclude the multiple zero $0$
when $y = 0$, $r \ge 2$).

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Theorem 1 (`integers-2025-A38-thm-1`).
