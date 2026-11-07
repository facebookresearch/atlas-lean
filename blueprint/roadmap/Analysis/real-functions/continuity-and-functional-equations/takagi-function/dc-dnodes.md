# Number of D-nodes of the divide-and-conquer tree

The number $\delta(n)$ of D-nodes in the
divide-and-conquer tree on $n$ leaves (OEIS A296062) is defined by the recurrence the paper
quotes from Coronado et al.: $\delta(1) = 0$, and for every natural number $m \ge 1$,
$\delta(2m) = 2\,\delta(m)$ and $\delta(2m+1) = \delta(m) + \delta(m+1) + 1$. The value at $0$
is the junk value $\delta(0) = 0$.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Theorem 9 (`exp_D_recursive`).
