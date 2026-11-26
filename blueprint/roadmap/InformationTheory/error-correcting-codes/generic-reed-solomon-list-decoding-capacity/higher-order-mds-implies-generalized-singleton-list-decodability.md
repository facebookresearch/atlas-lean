# Higher order MDS codes attain the generalized Singleton bound

For every $L \ge 1$, a linear $[n, k]$ code $C$ is $\mathrm{LD}$-$\mathrm{MDS}(\le L)$ if and only if its dual code $C^{\perp}$ is $\mathrm{MDS}(L+1)$. That is, $C^{\perp}$ is $\mathrm{MDS}(L+1)$ exactly when, for every $1 \le L' \le L$, every $y$ and all $L' + 1$ distinct codewords $c_0, \dots, c_{L'} \in C$,

$$
\sum_{j=0}^{L'} \mathrm{wt}(c_j - y) > L'(n - k) .
$$

In particular a code whose dual is $\mathrm{MDS}(L+1)$ is $\big(\frac{L}{L+1}\cdot\frac{n-k}{n}, L\big)$-list decodable and attains the generalized Singleton bound for list size $L$; this ordinary-radius statement is a consequence of the equivalence, not equivalent to it. $\mathrm{MDS}(\ell)$ is not preserved under duality for $\ell \ge 4$, so the dual cannot be dropped.

## Proof sketch

Let $H$ be a parity-check matrix of $C$, a generator matrix of $C^\perp$, and for $J \subseteq [n]$ let $H_J$ be the span of its columns indexed by $J$. Codewords $c_0, \dots, c_{L'}$ and a centre $y$ correspond to error vectors $u_j = y - c_j$ with a common syndrome $H u_j = H y$ and supports $J_j$, and the average-radius condition bounds $\sum_j |J_j|$. If $C^\perp$ is not $\mathrm{MDS}(L+1)$, some sets $J_0, \dots, J_L$ have $H_{J_0} \cap \dots \cap H_{J_L} \ne 0$ while the generic intersection is $0$; by the generic intersection-dimension formula $\sum_i |J_{P_i}| \le (s-1)(n-k)$ for every partition $P_1 \sqcup \dots \sqcup P_s$, and grouping equal vectors among the resulting $u_j$ gives $s \ge 2$ distinct vectors with total weight at most $(s-1)(n-k)$ and a common syndrome, violating $\mathrm{LD}$-$\mathrm{MDS}(s-1)$. Conversely, a violation of $\mathrm{LD}$-$\mathrm{MDS}(\ell - 1)$ by distinct $u_1, \dots, u_\ell$ of total weight at most $(\ell-1)(n-k)$ either reduces to a smaller list or yields an intersection $H_{J_1} \cap \dots \cap H_{J_\ell}$ of dimension larger than the generic one, so $C^\perp$ is not $\mathrm{MDS}(\ell)$.

## Depends on

- [Codes attaining the generalized Singleton bound (LD-MDS codes)](codes-attaining-the-generalized-singleton-bound.md)
- [Higher order MDS codes MDS(l)](higher-order-mds-codes.md)

## Sources

- Joshua Brakensiek, Sivakanth Gopi, Visu Makam, "Generic Reed-Solomon codes achieve list-decoding capacity", STOC (2023), SIAM Journal on Computing (2024); arXiv:2206.05256, Theorem 1.13 and Section 4.1.
- Ron M. Roth, "Higher-order MDS codes", IEEE Transactions on Information Theory 68(12) (2022).
