# Best-buddy edge weights for Hi-C scaffold graphs

Represent each contig by two nodes, its beginning $B$ and end $E$ (the halves of the contig on
either side of its midpoint), and let $V$ be the set of contig ends. For ends $u, v$ of different
contigs let $N(u, v)$ be the number of Hi-C read pairs with one read on each, and let $C(u)$ be the
number of restriction-enzyme cut sites on the contig carrying $u$. The **normalized Hi-C weight** is

$$W(u, v) \;=\; \frac{N(u, v)}{C(u) + C(v)},$$

defined when $C(u) + C(v) > 0$; it corrects for the fact that Hi-C read yield is proportional to the
number of cut sites. The
**best-buddy weight** of an edge is its weight relative to the strongest competing edge at either
endpoint,

$$\mathrm{BB}(u, v) \;=\; \frac{W(u, v)}{\max\bigl\{ W(x, y) : \{x, y\} \ne \{u, v\},\ \{x, y\} \cap \{u, v\} \ne \varnothing \bigr\}},$$

defined when this maximum exists and is positive, that is, when some competing edge at $u$ or $v$ has
positive weight; the source does not specify the remaining case, and the statements below concern
edges whose best-buddy weight is defined. Only edges with $\mathrm{BB}(u, v) > 1$ are retained. Hence
a retained edge is the unique heaviest edge incident to both $u$ and $v$, so the retained edges form a
matching. If
the largest and second-largest incident weights are stored at each node, all best-buddy weights
are computed in $O(|E|)$ time.

## Remarks

$\mathrm{BB}(u, v) > 1$ means $W(u, v)$ exceeds every other edge weight at $u$ and at $v$, so no two
retained edges share an endpoint. A global weight threshold fails because contact frequencies vary
across the genome; the ratio compares an edge only with its local competitors, which is robust to
such variation. Retained edges are consumed, and in subsequent iterations edges that were initially
dominated can become best buddies. An analogous ratio is used for edges supported by the assembly
graph: the ratio of the second-shortest to the shortest path length over the four orientations of a
contig pair, again retaining edges with ratio above $1$.

## Sources

- J. Ghurye, A. Rhie, B. P. Walenz et al., "Integrating Hi-C links with assembly graphs for chromosome-scale assembly", *PLoS Computational Biology* 15 (2019) e1007273, <https://doi.org/10.1371/journal.pcbi.1007273> (PMC6719893), Methods, "Scaffold graph construction" (definitions of $W(u,v)$ and $\mathrm{BB}(u,v)$, retention of edges with $\mathrm{BB} > 1$, $O(|E|)$ computation).
