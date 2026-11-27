# Wired lifts along connected surjective digraph maps of phylogenetic networks

**Setting.** For a finite taxon set $X$, an **$X$-network** $N=(V,A,r,X)$ is a rooted digraph whose leaves are identified bijectively with $X$ and in which every vertex has a directed path to a leaf. An **$X$-digraph map** $f:N\to N'$ between $X$-networks fixes the root and every leaf and sends each arc $(u,v)$ either to an arc $(f(u),f(v))$ of $N'$ or to a single vertex ($f(u)=f(v)$, the arc is collapsed). It is a **CSD map** (connected surjective digraph map) if it is surjective on vertices and arcs and every fiber $f^{-1}(v')$ is connected in the underlying undirected graph $\mathrm{Und}(N)$. For example, contracting a set of arcs is a CSD map.

**Theorem (structure of CSD maps).** Let $f:N\to N'$ be a CSD map.

1. Preimages of connected vertex sets of $N'$ are connected in $N$; compositions of CSD maps are CSD maps.
2. There is a set $B$ of arcs of $N$ whose successive contraction yields a network $X$-isomorphic to $N'$. Equivalently, $N'\cong N/{\sim}$ where $u\sim v\iff f(u)=f(v)$, a leaf-preserving partition into connected classes.

**Wired lift.** A wired lift of $N'$ into $N$ is an undirected subgraph $M=(W,E)$ of $\mathrm{Und}(N)$ such that: (i) for each arc $(u',v')$ of $N'$ exactly one arc $(u,v)$ of $N$ with $f(u)=u'$, $f(v)=v'$ has $\{u,v\}\in E$ (these form the non-degenerate edges $E_1$); (ii) every other edge of $M$ joins two vertices with the same image; (iii) for each vertex $v'$ of $N'$ the induced subgraph $M[f^{-1}(v')\cap W]$ is a tree whose leaves lie among the endpoints of $E_1$ and the taxa.

**Theorem (wired lifts).** Let $f:N\to N'$ be a CSD map, and for each arc $(u',v')$ of $N'$ choose any arc $(u,v)$ of $N$ over it, giving an edge set $E_1$. Then $f$ has a wired lift with non-degenerate edge set exactly $E_1$, and every wired lift is a resolution of $\mathrm{Und}(N')$ (it becomes $\mathrm{Und}(N')$ after contracting each fiber tree to a point). Consequently:

- if $U'$ is a subgraph of $\mathrm{Und}(N')$ with all total degrees at most $3$, then $\mathrm{Und}(N)$ contains a subgraph homeomorphic to $U'$; in particular every quartet $ab|cd$ displayed (as a homeomorphic subgraph) by $\mathrm{Und}(N')$ is displayed by $\mathrm{Und}(N)$;
- if $U$ and $T$ are rooted $X$-trees and $f:U\to T$ is CSD, every rooted triple $ab|c$ of $T$ is a rooted triple of $U$, and if $T$ is binary then $U$ and $T$ are homeomorphic.

On the other hand, without connectivity of fibers the constraint disappears: every acyclic $X$-network is the image of a surjective digraph map from a network homeomorphic to a star.

## Expansion

Item 2 follows by contracting, one at a time, arcs inside fibers: connectivity of each fiber guarantees that a spanning tree of the fiber exists in $\mathrm{Und}(N)$ and its arcs can be contracted without creating new adjacencies, yielding the quotient by $\sim$, which is isomorphic to $N'$ by surjectivity on arcs. For the wired lift, start from the chosen edges $E_1$ and, in each fiber $f^{-1}(v')$, connect the endpoints of $E_1$ lying in that fiber (and the taxon, if $v'$ is a leaf) by a minimal subtree of the connected fiber; minimal Steiner trees have their leaves among the terminals, giving property (iii). Contracting each fiber tree recovers $\mathrm{Und}(N')$ edge for edge, so $M$ resolves $N'$. A subgraph $U'$ of maximum degree $3$ lifts to a homeomorphic copy because at each vertex at most three branches meet inside a fiber tree, which can be routed through a single branching point; with degree $4$ the fiber tree may split the vertex, which is why quartets survive but higher-degree structure need not.

## Sources

- Stephen J. Willson, "CSD Homomorphisms Between Phylogenetic Networks", arXiv (2010). Section 2 (X-networks), Section 3 (Theorems 3.1–3.6: quotients, connected preimages, composition, contraction), Section 4 (definition of wired lift, Theorem 4.1, Corollaries 4.2 and 4.3, Theorems 4.4 and 4.5). <https://doi.org/10.48550/arXiv.1005.2108>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 9(4) (2012), 1128–1138, <https://doi.org/10.1109/tcbb.2012.52>; locators above refer to the arXiv version.
