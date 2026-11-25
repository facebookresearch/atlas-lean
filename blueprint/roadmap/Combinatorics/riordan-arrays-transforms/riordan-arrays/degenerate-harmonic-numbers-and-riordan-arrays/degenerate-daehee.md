# Degenerate Daehee numbers

For a real number $\lambda$ and $n \in \mathbb{N}$, the
degenerate Daehee number is $D_{n,\lambda} = n! \binom{\lambda}{n+1} / \lambda$, where
$\binom{\lambda}{k} = \lambda (\lambda - 1) \cdots (\lambda - k + 1) / k!$ is the generalized
binomial coefficient (for $\lambda = 0$ the value is $0$, by the convention $x / 0 = 0$).

For $\lambda \ne 0$ the degenerate logarithm $\log_\lambda(1 + t) = ((1 + t)^\lambda - 1) / \lambda$
satisfies $\log_\lambda(1 + t) / t = \sum_{n \ge 0} \binom{\lambda}{n+1} t^n / \lambda$, so the
numbers $D_{n,\lambda}$ are given by
$\log_\lambda(1 + t) / t = \sum_{n \ge 0} D_{n,\lambda} \, t^n / n!$.

## Sources

- Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equations (2) and (9).
