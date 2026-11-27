# Greedy matching layout of contigs

Let $G = (V, E)$ be a graph on contig ends whose edges $e$ join ends of different contigs and carry
positive weights $w(e)$ (for example
[best-buddy weights](best-buddy-edge-weights-for-hi-c-scaffold-graphs.md)), and let $I$ be the set of
implicit edges joining the two ends of each contig. For any matching $M \subseteq E$, the graph
$(V, M \cup I)$ has maximum degree $2$, so its components are paths and cycles; after deleting the
lowest-weight edge of $M$ from each cycle, each path is a scaffold, that is, an ordered and oriented
sequence of contigs. The **greedy matching** scans $E$ in non-increasing order of weight and adds an
edge whenever neither endpoint is already matched. It runs in $O(|E|)$ time after sorting, its
output $M_g$ is a maximal matching, and

$$w(M_g) \;\ge\; \tfrac12\, w(M^*)$$

for every maximum-weight matching $M^*$ of $G$. Since $M_g$ is maximal, no edge of $G$ joins two
vertices left unmatched by $M_g$, so a second greedy pass over the unmatched vertices of the same
graph adds nothing.

## Depends on

- [Best-buddy edge weights for Hi-C scaffold graphs](best-buddy-edge-weights-for-hi-c-scaffold-graphs.md)

## Proof sketch

Each node meets at most one edge of $M$ and exactly one implicit edge, giving degree at most $2$.
For the approximation bound, charge every edge $e^* \in M^*$ to the first edge $g \in M_g$ chosen by
the greedy scan that shares an endpoint with $e^*$; such a $g$ exists by maximality, and
$w(g) \ge w(e^*)$ because $e^*$ was still available when $g$ was chosen. Each $g$ has two endpoints
and each endpoint is met by at most one edge of $M^*$, so at most two edges of $M^*$ are charged to
$g$, giving $w(M^*) \le 2\, w(M_g)$. An exact maximum-weight matching per round would cost
$O(|E||V|^2)$, so the greedy rule trades a factor of two in the objective for linear time per round.

The source's scaffolder applies this one-pass step repeatedly, but to a changing graph, so the
guarantee above holds within each round only. After a round, edges that were used are removed,
best-buddy weights are recomputed on what remains, so that initially dominated edges can become best
buddies, and the joins of the round are checked for mis-joins, incorrect ones being broken and their
edges blacklisted for later rounds. The iteration stops when the majority of the joins made in the
previous round are incorrect.

## Sources

- J. Ghurye, A. Rhie, B. P. Walenz et al., "Integrating Hi-C links with assembly graphs for chromosome-scale assembly", *PLoS Computational Biology* 15 (2019) e1007273, <https://doi.org/10.1371/journal.pcbi.1007273> (PMC6719893), Methods, "Contig layout" and Algorithm 1 (layout as weighted maximum matching, greedy maximal matching within a factor $1/2$ of the optimum, removal of cycles by deleting the lowest-weight non-implicit edge).
- D. Avis, "A survey of heuristics for the weighted matching problem", *Networks* 13 (1983) (the greedy $1/2$-approximation).
