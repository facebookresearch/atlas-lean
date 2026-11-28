# Phase bound for shortest-augmenting-path matching algorithms in general graphs

Let $G$ be a finite simple graph, not necessarily bipartite, with matching number $s = \nu(G)$. Consider any algorithm that starts from the empty matching and in each phase augments along a maximal family of vertex-disjoint shortest augmenting paths of the current matching. Then the length of a shortest augmenting path strictly increases from each phase to the next, and the algorithm reaches a maximum matching after $O(\sqrt{n})$ phases, where $n$ is the number of vertices (Hopcroft and Karp; in bipartite graphs at most $2\sqrt{n}$ phases). Explicitly, the proof sketch derives from the three linked Hopcroft–Karp lemmas the bound $\lceil \sqrt{s} \, \rceil + \lfloor \sqrt{s} \, \rfloor$ on the number of phases.

## Proof sketch

By the Hopcroft-Karp inequality $|q| \ge |p| + |E(p) \cap E(q)|$ for successive augmentations, valid in every simple graph, shortest augmenting lengths never decrease, equal lengths give vertex-disjoint paths, and maximality of the family forces a strict increase after each phase. After $k = \lceil \sqrt{s} \rceil$ phases the shortest augmenting path has length at least $2k + 1$, while the short-augmenting-path corollary bounds it by $2\lfloor r/(s - r) \rfloor + 1$ for the current size $r$; hence $s - r \le r/k \le \sqrt{s}$. Each later phase raises $r$ by at least one, so at most $\lfloor \sqrt{s} \rfloor$ further phases remain. In total there are at most

$$
\lceil \sqrt{s} \, \rceil + \lfloor \sqrt{s} \, \rfloor \le 2\sqrt{s} + 1 \le \sqrt{2n} + 1
$$

phases, using $s \le n/2$.

## Depends on

- [Augmenting path](../berge-s-lemma/is-augmenting-walk.md)

## Proof depends on

- [Augmenting after a shortest augmentation (Hopcroft–Karp, Theorem 2)](../berge-s-lemma/length-add-card-inter-le.md)
- [A short augmenting path exists (Hopcroft–Karp, Corollary 2)](../berge-s-lemma/exists-is-augmenting-walk-length-le.md)
- [Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1)](../berge-s-lemma/exists-disjoint-augmenting-walks.md)

## Sources

- J. E. Hopcroft, R. M. Karp, "An n^{5/2} algorithm for maximum matchings in bipartite graphs", SIAM Journal on Computing 2 (1973).
- N. Blum, "Maximum Matching in General Graphs Without Explicit Consideration of Blossoms Revisited", arXiv:1509.04927, Section 3 (Hopcroft and Karp's $O(\sqrt{n})$ phase bound in general graphs).
- U. Zwick, "Lecture notes on: Maximum matching in bipartite and non-bipartite graphs", Tel Aviv University, Section 5 (Lemma 5.1 in arbitrary graphs and Theorem 5.3: at most $2\sqrt{n}$ phases in bipartite graphs).
- S. Micali, V. V. Vazirani, "An O(sqrt(|V|) |E|) algorithm for finding maximum matching in general graphs", FOCS (1980).
