# Distances from the source never decrease along Edmonds–Karp (Proposition 3, iterated)

Notation: $f_i$ is the $i$-th iterate of the algorithm's [step](step.md) from a starting integer matrix $f_0$ (any integer matrix, not necessarily skew-symmetric or feasible), $N_i$ its residual graph, and $P_i$ the [path used by step $i$](step-path.md). If $i \le j$, every walk of length $k$ from $s$ to a vertex $u$ in $N_j$ can be replaced by a walk of length at most $k$ from $s$ to $u$ in $N_i$: $\delta_i(s, u) \le \delta_j(s, u)$.

## Informally uses

- [One Edmonds–Karp step does not shorten distances from the source (Proposition 3 (1))](walk-step-source.md): applied $j - i$ times.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 1–3, Lemmas 1 and 2, Theorem 1).
