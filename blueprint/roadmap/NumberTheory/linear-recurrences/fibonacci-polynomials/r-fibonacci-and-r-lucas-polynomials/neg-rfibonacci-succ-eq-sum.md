# Explicit sum for the (-r)-Fibonacci polynomials

Let $A$ be a commutative ring,
$r \ge 2$, $x \in A$ and $y$ a unit of $A$, and write $U_n = U^{(-r)}_n(x, y)$. For every
$n \ge 0$,

$$U_{n+1} = \sum_{k=0}^{\lfloor n/r \rfloor} \binom{k}{n - rk} y^{-k} (-x)^{n-rk},$$

where $\binom{a}{b} = 0$ for $b > a$, so the terms with $(r+1) k < n$ vanish.

The paper states $n \ge 1$ and $x$ a unit; the identity holds for $n = 0$ and every $x$.

## Sources

- Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, Theorem 6 (`integers-2025-A38-thm-6`).
