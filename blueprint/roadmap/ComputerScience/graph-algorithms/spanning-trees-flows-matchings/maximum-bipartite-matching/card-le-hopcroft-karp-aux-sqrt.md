# Hopcroft and Karp's bound on the number of phases

In a bipartite graph with $b$ right
vertices, run at most $2 \lfloor \sqrt{b} \rfloor + 2$ Hopcroft–Karp phases from the empty
matching, stopping early when a phase finds no augmenting path. Then no matching of the graph has
more edges than the resulting one.

After the first $\lfloor \sqrt{b} \rfloor + 1$ phases every augmenting path has more than
$\lfloor \sqrt{b} \rfloor$ pairs, so the deficit against any matching is at most
$\lfloor \sqrt{b} \rfloor$, and each further phase adds an edge.

Hopcroft and Karp bound the number of phases by $2\lfloor\sqrt{s}\rfloor + 2$, where $s$ is the size of a maximum matching (their Theorem 3 and Corollary 5). The bound here uses the number $b$ of right vertices instead; since $s \le b$ it is weaker for graphs whose maximum matchings leave right vertices unmatched, and equal when a matching covers all right vertices. The deficit step also differs: Hopcroft and Karp count with their Theorem 1 and Corollary 2 (disjoint augmenting paths in a symmetric difference), whereas the proof here covers the edges by the unreached left vertices and the reached right vertices of each round of the search.

## Background

- [A short augmenting path exists (Hopcroft–Karp, Corollary 2)](../../../../GraphTheory/matchings-and-flows/berge-s-lemma/exists-is-augmenting-walk-length-le.md): the general-graph counting step of the original proof.

## Sources

- J. E. Hopcroft and R. M. Karp, "An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs", *SIAM Journal on Computing* 2(4) (1973), 225–231, §2, Theorem 3 and Corollary 5.
