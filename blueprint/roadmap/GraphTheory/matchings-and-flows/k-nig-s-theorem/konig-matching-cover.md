# Kőnig's theorem for finite bipartite graphs

Every bipartite simple graph $G$ on a finite vertex
type $V$ has a matching $M$ and a vertex cover $C \subseteq V$ such that the number of edges of $M$
equals the number of vertices in $C$.

## Sources

- D. Kőnig (1931); J. Egerváry (1931) weighted form. It follows from `konig_matching_cover_general`; the instances `[DecidableEq V]` and `[DecidableRel G.Adj]` are unused and keep the source's shape.
