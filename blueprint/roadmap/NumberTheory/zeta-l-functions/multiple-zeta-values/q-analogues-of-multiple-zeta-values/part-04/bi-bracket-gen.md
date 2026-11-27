# Generating series of bi-brackets

For $r \in \mathbb{N}$, the generating series of the
bi-brackets of depth $r$ is the formal power series in the variables $X_1, \dots, X_r$,
$Y_1, \dots, Y_r$ with coefficients in $\mathbb{Q}[[q]]$

$$
g(X_1, \dots, X_r; Y_1, \dots, Y_r) =
\sum_{k_1, \dots, k_r \ge 1} \, \sum_{d_1, \dots, d_r \ge 1}
g(k_1, \dots, k_r; d_1 - 1, \dots, d_r - 1) \prod_{j=1}^{r} X_j^{k_j - 1} Y_j^{d_j - 1},
$$

where $g(k_1, \dots, k_r; d_1, \dots, d_r)$ is the bi-bracket. Equivalently, the coefficient of
$\prod_{j=1}^{r} X_j^{a_j} Y_j^{b_j}$ is $g(a_1 + 1, \dots, a_r + 1; b_1, \dots, b_r)$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 11 (definition of the generating series).
