# Variance of the gamete contributions

For a parent map
`parent : Fin (2 * N) → Fin N` with contributions $n_i$ (`gameteContribution`), the variance
$V_n = \frac1N \sum_i (n_i - 2)^2$ of the contributions about their mean $2$ (the contributions
sum to $2N$). For $N = 0$ the value is $0$, by Lean's convention $x / 0 = 0$.
