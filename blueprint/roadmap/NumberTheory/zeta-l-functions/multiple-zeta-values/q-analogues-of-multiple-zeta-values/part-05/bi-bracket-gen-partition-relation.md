# Partition relation for bi-brackets

For every natural number $r$, the generating series
$g(X_1, \dots, X_r; Y_1, \dots, Y_r)$ of bi-brackets of depth $r$ satisfies

$$g(X_1, \dots, X_r; Y_1, \dots, Y_r) = g(Y_1 + \dots + Y_r, \dots, Y_1 + Y_2, Y_1;
X_r, X_{r-1} - X_r, \dots, X_1 - X_2),$$

where the right side substitutes linear forms into $g$ simultaneously: for $1 \le i \le r$, the
variable $X_i$ is replaced by $Y_1 + \dots + Y_{r+1-i}$ and the variable $Y_i$ by
$X_{r+1-i} - X_{r+2-i}$, with $X_{r+1} := 0$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 12 (partition relation, after Bachmann).
