# Degenerate Stirling numbers of the second kind

For a real number $\lambda$, let
$e_\lambda(t) = \sum_{n \ge 0} (1)_{n,\lambda} t^n / n!$ be the degenerate exponential series,
where $(1)_{0,\lambda} = 1$ and $(1)_{n,\lambda} = 1 (1 - \lambda) \cdots (1 - (n - 1)\lambda)$.
For natural numbers $n$ and $k$, the degenerate Stirling number of the second kind
$S_{2,\lambda}(n, k)$ is $n!/k!$ times the coefficient of $t^n$ in $(e_\lambda(t) - 1)^k$.
Equivalently, $(e_\lambda(t) - 1)^k / k! = \sum_{n \ge k} S_{2,\lambda}(n, k) t^n / n!$, and
$S_{2,\lambda}(n, k) = 0$ for $n < k$.

## Sources

- Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (8).
