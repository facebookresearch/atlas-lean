# Between two uses of a bottleneck arc, its reverse is used (Edmonds–Karp, Lemma 1)

Notation: $f_i$ is the $i$-th iterate of the algorithm's [step](step.md) from a starting integer matrix $f_0$ (any integer matrix, not necessarily skew-symmetric or feasible), $N_i$ its residual graph, and $P_i$ the [path used by step $i$](step-path.md). Let $i < j$, let $t$ be reachable in $N_i$, let $(u, v)$ be a bottleneck arc of $P_i$, and let $(u, v)$ be an arc of $N_j$. Then there is an $l$ with $i < l < j$ such that $t$ is reachable in $N_l$ and $(v, u)$ is a step of $P_l$.

Edmonds and Karp assume that $(u, v)$ is a bottleneck arc of $P_j$ as well; their proof only uses that $(u, v)$ is then an arc of $N_j$, which is the hypothesis here, so the statement is slightly more general. The proof is theirs: take the first $l + 1 > i$ at which $(u, v)$ is residual again; by Proposition 1, $l > i$, and by Proposition 2 the arc can only have reappeared as the reverse of a step of $P_l$.

## Informally uses

- [A bottleneck arc is saturated (Edmonds–Karp, Proposition 1)](not-edge-iterate-succ-of-bottleneck.md): $(u, v)$ is not residual right after step $i$.
- [New residual arcs reverse the augmenting path (Edmonds–Karp, Proposition 2)](residual-graph-edge-augment.md): the step at which $(u, v)$ reappears.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 1–3, Lemmas 1 and 2, Theorem 1).
