# A bottleneck arc is saturated (Edmonds–Karp, Proposition 1)

Notation: $f_i$ is the $i$-th iterate of the algorithm's [step](step.md) from a starting integer matrix $f_0$ (any integer matrix, not necessarily skew-symmetric or feasible), $N_i$ its residual graph, and $P_i$ the [path used by step $i$](step-path.md). If $t$ is reachable in $N_i$ and $(u, v)$ is a bottleneck arc of $P_i$ (a step whose residual capacity equals the bottleneck), then $(u, v)$ is not an arc of $N_{i+1}$: the augmentation raises the flow entry on $(u, v)$ to $c(u, v)$.

## Informally uses

- [Augmentation adds exactly the amount on the steps of a duplicate-free path](edge-delta-eq-one-of-mem.md): shortest paths have no repeated vertex.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 1–3, Lemmas 1 and 2, Theorem 1).
