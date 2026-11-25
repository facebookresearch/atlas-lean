# Edmonds–Karp augmentation count, sharp form

Let $s \ne t$ be vertices of a network on $n$ vertices with natural-number capacities. If $t$ is reachable from $s$ in the residual graphs of the first $m$ iterates of the Edmonds–Karp [step](step.md), starting from any integer matrix (not necessarily skew-symmetric or feasible), then

$$m \le \binom{n}{2} \left\lfloor \frac{n}{2} \right\rfloor .$$

Every augmentation has a bottleneck arc, and hence an unordered bottleneck pair $\{u, v\}$ of distinct vertices. If two augmentations $i < j$ have the same bottleneck pair, then $|P_j| \ge |P_i| + 2$: when the orientations agree, Lemma 1 gives an intermediate step using the reverse arc and Lemma 2 with the monotonicity of path lengths applies; when they are opposite, Lemma 2 applies directly. Path lengths lie between $2$ and $n$ entries, so the map sending a step to its bottleneck pair and to $\lfloor |P_i| / 2 \rfloor$ is injective into a set with $\binom{n}{2} \lfloor n/2 \rfloor$ elements.

This is Edmonds and Karp's counting argument, organised as an injection; it gives a slightly sharper bound than their count $\binom{n}{2} \cdot \frac{n + 1}{2} = \frac{n^3 - n}{4}$, since each pair is a bottleneck at most $\lfloor n/2 \rfloor \le \frac{n + 1}{2}$ times.

## Informally uses

- [The bottleneck of a path is attained](exists-mem-path-edges-residual-amount-eq.md): every augmentation has a bottleneck arc.
- [Between two uses of a bottleneck arc, its reverse is used (Edmonds–Karp, Lemma 1)](exists-reverse-between-of-bottleneck.md)
- [Using an arc and then its reverse costs two arcs (Edmonds–Karp, Lemma 2)](length-add-two-le-of-reverse.md)
- [Shortest augmenting paths never get shorter](length-step-path-le-of-le.md)

## Sources

- J. Edmonds and R. M. Karp, "Theoretical improvements in algorithmic efficiency for network flow problems", *Journal of the ACM* 19(2) (1972), 248–264, §1.2 (Propositions 1–3, Lemmas 1 and 2, Theorem 1).
