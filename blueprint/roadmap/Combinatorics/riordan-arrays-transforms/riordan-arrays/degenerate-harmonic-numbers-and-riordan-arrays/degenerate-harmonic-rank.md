# Generalized degenerate harmonic numbers of a given rank

For real $\lambda$ and $\alpha$,
let $\ell_0 = 0$ and $\ell_m = (-1)^{m-1} \binom{\lambda}{m} / (\lambda \alpha^m)$ for $m \ge 1$,
where $\binom{\lambda}{m}$ is the generalized binomial coefficient and a quotient by $0$ is read
as $0$, and let $L(t) = \sum_{m \ge 0} \ell_m t^m$ as a formal power series. For
$\lambda, \alpha > 0$ this is the expansion of $-\log_\lambda(1 - t/\alpha)$, where
$\log_\lambda(1 + t) = ((1 + t)^\lambda - 1)/\lambda$ is the degenerate logarithm. For natural
numbers $n$ and $r$, the generalized degenerate harmonic number of rank $r$, written
$H_\lambda(n, r, \alpha)$, is the sum of the coefficients of $t^0, t^1, \dots, t^n$ in
$L(t)^{r+1}$. Equivalently, $\sum_{n \ge 0} H_\lambda(n, r, \alpha) t^n = L(t)^{r+1} / (1 - t)$.

Expanding the power, $H_\lambda(n, r, \alpha)$ is the sum of $\ell_{k_0} \cdots \ell_{k_r}$ over
all $k_0, \dots, k_r \ge 1$ with $k_0 + \cdots + k_r \le n$, which is the explicit definition in
the source.

## Sources

- Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1, Equation (5).
