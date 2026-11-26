# Degenerate Bernoulli numbers

For a real number $\lambda$, let $(1)_{0,\lambda} = 1$ and
$(1)_{m,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (m - 1)\lambda)$ for $m \ge 1$ (the
generalized falling factorial of $1$ with increment $\lambda$). For $n \in \mathbb{N}$, the
degenerate Bernoulli number $\beta_{n,\lambda}$ is $n!$ times the coefficient of $t^n$ in the
inverse of the formal power series $\sum_{m \ge 0} (1)_{m+1,\lambda} \, t^m / (m + 1)!$ over
$\mathbb{R}$, whose constant term is $1$.

Since this power series is $(e_\lambda(t) - 1) / t$ for the degenerate exponential series
$e_\lambda(t)$, the numbers $\beta_{n,\lambda}$ satisfy
$t / (e_\lambda(t) - 1) = \sum_{n \ge 0} \beta_{n,\lambda} \, t^n / n!$.

## Sources

- Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (6).
