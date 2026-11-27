# Shortest augmenting paths never get shorter

Notation: $f_i$ is the $i$-th iterate of the algorithm's [step](step.md) from a starting integer matrix $f_0$ (any integer matrix, not necessarily skew-symmetric or feasible), $N_i$ its residual graph, and $P_i$ the [path used by step $i$](step-path.md). If $i \le j$ and $t$ is reachable from $s$ in $N_i$ and in $N_j$, then $P_i$ has at most as many entries as $P_j$: the length $\delta_i(s, t)$ of the shortest augmenting path is nondecreasing in $i$.

## Informally uses

- [Distances from the source never decrease along Edmonds–Karp (Proposition 3, iterated)](walk-iterate-step-source.md): with $u = t$.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 1–3, Lemmas 1 and 2, Theorem 1).
