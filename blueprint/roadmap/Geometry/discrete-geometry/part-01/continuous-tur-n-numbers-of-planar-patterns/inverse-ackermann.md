# Inverse Ackermann function

For a natural number $n$, the inverse Ackermann function
$\alpha(n)$ is the least natural number $k$ with $n \le A(k, k)$, where $A$ is the two-argument
Ackermann function, given for all natural numbers $m$ and $j$ by $A(0, j) = j + 1$,
$A(m + 1, 0) = A(m, 1)$ and $A(m + 1, j + 1) = A(m, A(m + 1, j))$.

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 3.2 (the inverse Ackermann function `α(n)` in Keszegh's bound quoted before Corollary 3.8).
