# The per-clause inequality behind the 3/4 guarantee

For every $k \ge 1$,

$$\left(1 - 2^{-k}\right) + \beta_k \ge \frac32 .$$

Equality holds for $k = 1$ ($\frac12 + 1$) and $k = 2$ ($\frac34 + \frac34$). For $k \ge 3$,
$1 - 2^{-k} \ge \frac78$ and $(1 - 1/k)^k \le e^{-1} \le \frac38$, so the sum is at least $\frac32$.
Johnson's assignment is strong on long clauses and randomized rounding on short ones; this
inequality is why their average never loses more than a quarter.

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), proof of Theorem 4.1.
