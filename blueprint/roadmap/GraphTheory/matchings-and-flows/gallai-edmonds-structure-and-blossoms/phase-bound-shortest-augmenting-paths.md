# Phase bound for shortest-augmenting-path matching algorithms in general graphs

Let $G$ be a finite simple graph, not necessarily bipartite, with matching number $s = \nu(G)$. Consider any algorithm that starts from the empty matching and in each phase augments along a maximal family of vertex-disjoint shortest augmenting paths of the current matching. Then the length of a shortest augmenting path strictly increases from each phase to the next, and the algorithm reaches a maximum matching after at most

$$
\lceil \sqrt{s} \, \rceil + \lfloor \sqrt{s} \, \rfloor \le 2\sqrt{s} + 1 \le \sqrt{2n} + 1
$$

phases, where $n$ is the number of vertices.

## Proof sketch

By the Hopcroft-Karp inequality $|q| \ge |p| + |E(p) \cap E(q)|$ for successive augmentations, valid in every simple graph, shortest augmenting lengths never decrease, equal lengths give vertex-disjoint paths, and maximality of the family forces a strict increase after each phase. After $k = \lceil \sqrt{s} \rceil$ phases the shortest augmenting path has length at least $2k + 1$, while the short-augmenting-path corollary bounds it by $2\lfloor r/(s - r) \rfloor + 1$ for the current size $r$; hence $s - r \le r/k \le \sqrt{s}$. Each later phase raises $r$ by at least one, so at most $\lfloor \sqrt{s} \rfloor$ further phases remain.

## Depends on

- [Augmenting path](../berge-s-lemma/is-augmenting-walk.md)

## Proof depends on

- [Augmenting after a shortest augmentation (Hopcroft–Karp, Theorem 2)](../berge-s-lemma/length-add-card-inter-le.md)
- [A short augmenting path exists (Hopcroft–Karp, Corollary 2)](../berge-s-lemma/exists-is-augmenting-walk-length-le.md)
- [Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1)](../berge-s-lemma/exists-disjoint-augmenting-walks.md)

## Sources

- J. E. Hopcroft, R. M. Karp, "An n^{5/2} algorithm for maximum matchings in bipartite graphs", SIAM Journal on Computing 2 (1973).
- S. Micali, V. V. Vazirani, "An O(sqrt(|V|) |E|) algorithm for finding maximum matching in general graphs", FOCS (1980).
