# Using an arc and then its reverse costs two arcs (Edmonds–Karp, Lemma 2)

Notation: $f_i$ is the $i$-th iterate of the algorithm's [step](step.md) from a starting integer matrix $f_0$ (any integer matrix, not necessarily skew-symmetric or feasible), $N_i$ its residual graph, and $P_i$ the [path used by step $i$](step-path.md). If $i \le j$, $t$ is reachable in $N_i$ and in $N_j$, $(u, v)$ is a step of $P_i$ and $(v, u)$ a step of $P_j$, then $P_j$ has at least two more entries than $P_i$: $\delta_j(s, t) \ge \delta_i(s, t) + 2$.

Edmonds and Karp state the lemma for $i < j$; for $i = j$ the hypotheses cannot hold. Proof: $\delta_j(s, t) = \delta_j(s, v) + 1 + \delta_j(u, t) \ge \delta_i(s, v) + 1 + \delta_i(u, t) = (\delta_i(s, u) + 1) + 1 + (\delta_i(v, t) + 1) = \delta_i(s, t) + 2$, using the monotonicity of distances and the fact that $(u, v)$ lies on the shortest path $P_i$.

## Informally uses

- [Distances from the source never decrease along Edmonds–Karp (Proposition 3, iterated)](walk-iterate-step-source.md): $\delta_i(s, v) \le \delta_j(s, v)$.
- [Distances to the sink never decrease along Edmonds–Karp (Proposition 3, iterated)](walk-iterate-step-sink.md): $\delta_i(u, t) \le \delta_j(u, t)$.
- [A step of a chain splits it into two walks](exists-split-of-mem-path-edges.md): the positions of $(u, v)$ on $P_i$ and of $(v, u)$ on $P_j$.

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 1–3, Lemmas 1 and 2, Theorem 1).
