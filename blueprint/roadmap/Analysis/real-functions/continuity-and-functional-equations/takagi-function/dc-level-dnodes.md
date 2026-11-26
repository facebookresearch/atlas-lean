# Level counts of D-nodes

For natural numbers $n$ and $i$, let $n_i$ be the binary digit
of $n$ at position $i$ (the coefficient of $2^i$ in the binary expansion of $n$). The value
$\lambda_i(n)$ is $n \bmod 2^i$ if $n_i = 0$, and $2^i - (n \bmod 2^i)$ if $n_i = 1$.

For $n > 0$ and $i < \lfloor \log_2 n \rfloor$, this formula counts the D-nodes on level $i$ of
the divide-and-conquer tree on $n$ leaves. Outside this range the same formula applies and can
give a nonzero value even when the level has no D-nodes.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Theorem 11.
