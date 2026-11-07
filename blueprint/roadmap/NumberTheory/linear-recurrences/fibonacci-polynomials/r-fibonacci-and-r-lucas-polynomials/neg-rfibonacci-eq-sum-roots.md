# Binet formula for the (-r)-Fibonacci polynomials

Let $K$ be a field, $r \ge 2$,
$x \in K$ and $y \in K$ nonzero, and write $U_n = U^{(-r)}_n(x, y)$. Suppose that
$\beta_0, \dots, \beta_r \in K$ are pairwise distinct and that
$t^{r+1} - y^{-1} t + x y^{-1} = \prod_{k=0}^{r} (t - \beta_k)$ as polynomials over $K$. Then for
every $n \ge 0$,

$$U_{n+1} = \sum_{k=0}^{r} \frac{\beta_k^{n+r+1}}{r \beta_k^{r+1} - x y^{-1}},$$

where a term whose denominator vanishes is read as $0$.

The paper's hypothesis $x \ne \frac{r}{r+1} ((r+1) y)^{-1/r}$ is replaced by the distinctness of
the zeros (compare Lemma 1).

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Theorem 9 (`integers-2025-A38-thm-9`).
