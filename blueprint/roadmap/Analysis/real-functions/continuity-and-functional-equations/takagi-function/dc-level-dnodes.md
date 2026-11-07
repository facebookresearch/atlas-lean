# Level counts of D-nodes

For natural numbers $n$ and $i$, let $n_i$ be the binary digit
of $n$ at position $i$ (the coefficient of $2^i$ in the binary expansion of $n$). The level count
$\lambda_i(n)$ is $n \bmod 2^i$ if $n_i = 0$, and $2^i - (n \bmod 2^i)$ if $n_i = 1$.

This is the paper's closed form for the number of D-nodes on level $i$ of the
divide-and-conquer tree on $n$ leaves.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Theorem 11 (`exp_D_closed`).
