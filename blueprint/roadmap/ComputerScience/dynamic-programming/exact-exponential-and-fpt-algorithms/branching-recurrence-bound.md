# Branching-vector bound for search-tree recurrences

Let $(a_1, \dots, a_b)$ be a branching vector with branching factor $r \ge 1$ and let $C \ge 0$. If $T : \mathbb{N} \to \mathbb{R}_{\ge 0}$ satisfies

$$
T(n) \le \max\Big(C,\; \sum_{i\,:\,a_i \le n} T(n - a_i)\Big) \quad \text{for all } n,
$$

then $T(n) \le C\, r^n$ for all $n$. For an explicit search tree in which every internal node of measure $\mu$ has children of measures at most $\mu - a_{i}$ for a sublist of the branching vector, the number of leaves is at most $r^{\mu_0}$, the number of nodes at most $(\mu_0 + 1) r^{\mu_0}$, and if each node costs at most $W$ the total work is at most $W (\mu_0 + 1) r^{\mu_0}$, where $\mu_0$ is the root measure.

## Proof sketch

Strong induction on $n$: $\sum_i C r^{n - a_i} = C r^n \chi(r) \le C r^n$. The node bound sums the leaf bound over depths, since each root-to-node path has length at most $\mu_0$.

## Depends on

- [Branching vectors and branching factors](branching-vectors-and-factors.md)

## Sources

- F. V. Fomin and D. Kratsch, "Exact Exponential Algorithms", Springer, 2010.
- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
