# Polynomial functions on partitions characterize $\mathcal{Z}_q$

Let
$\mathcal{Z}_q = \mathcal{Z}_{q,0}$ be the space of general qMZVs, and for natural numbers $r$
and $N$ let $\mathcal{P}_r(N)$ be the set of partitions of $N$ of length $r$ in Stanley
coordinates. A power series $S = \sum_{N \ge 0} a_N q^N \in \mathbb{Q}[[q]]$ lies in
$\mathcal{Z}_q$ if and only if there are $f_0 \in \mathbb{Q}$, polynomials
$f_r \in \mathbb{Q}[X_1, \dots, X_r, Y_1, \dots, Y_r]$ for $r \ge 1$ and a natural number $R$
with $f_r = 0$ for every $r > R$, such that $a_0 = f_0$ and, for every $N \ge 1$,

$$a_N = \sum_{r=1}^{N} \sum_{(\mathbf{m}, \mathbf{n}) \in \mathcal{P}_r(N)}
f_r(\mathbf{m}, \mathbf{n}),$$

where $f_r(\mathbf{m}, \mathbf{n})$ is the value of $f_r$ at $X_i = m_i$, $Y_i = n_i$.

The sum over $r$ stops at $N$, which loses nothing because $\mathcal{P}_r(N)$ is empty for
$r > N$.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 19.
