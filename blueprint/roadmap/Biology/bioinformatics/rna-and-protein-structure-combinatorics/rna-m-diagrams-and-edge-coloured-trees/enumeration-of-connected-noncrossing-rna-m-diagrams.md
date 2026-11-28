# Enumeration of connected noncrossing RNA m-diagrams

**Objects.** Fix integers $k, m \ge 1$.
- An *$m$-edge-coloured tree* on $k$ vertices is a tree whose edges carry symbols $S_1,\dots,S_m$ so that no two edges at a vertex share a symbol; it is *labelled* if its vertices are labelled $1,\dots,k$. Each $S_r$ acts on vertices by swapping the endpoints of the $S_r$-edge (fixing vertices with no $S_r$-edge), and the **circular order** of a labelled tree $G$ is the permutation $\sigma_G = S_m S_{m-1}\cdots S_1$, which is always a $k$-cycle.
- An *RNA $m$-diagram of degree $k$* has $k$ vertices $1,\dots,k$ clockwise on a circle, each carrying the symbols $S_1,\dots,S_m$ clockwise; arcs join equal symbols at different vertices, each symbol used by at most one arc. It is *noncrossing* if it can be drawn without crossing arcs and *connected* if any two vertices are joined by a path (moving between symbols at a vertex is allowed). These are abstract RNA secondary structures in the circle representation, with each vertex a block of $m$ bases.
- An $m$-angulation of a regular $((m-2)k+2)$-gon divides it by diagonals into $k$ $m$-gons; it is *diagonal-coloured* if each $m$-gon has sides coloured $S_1,\dots,S_m$ clockwise.

**Theorem.**

*(1)* The following sets are in bijection: connected noncrossing RNA $m$-diagrams of degree $k$; rooted $m$-edge-coloured trees with $k$ vertices; labelled $m$-edge-coloured trees with $k$ vertices and circular order $(k\ k{-}1\ \cdots\ 1)$; rooted diagonal-coloured $m$-angulations of the $((m-2)k+2)$-gon up to rotation.

*(2)* Each of these sets has cardinality

$$T_{k,m} = \frac{m}{(m-2)k+2}\binom{(m-1)k}{k-1}.$$

*(3)* The total number of labelled $m$-edge-coloured trees with $k$ vertices is $U_{k,m} = \dfrac{m\,((m-1)k)!}{((m-2)k+2)!}$.

*(4)* (Induction classes) Two labelled $m$-edge-coloured trees on $k$ vertices are related by a sequence of chain-flip "induction" moves $L_i$, $R_i$ if and only if they have the same circular order; every unlabelled $m$-edge-coloured tree shape occurs in each such class.

## Expansion

Reading the arcs of a noncrossing diagram as edges coloured by their symbol gives an $m$-edge-coloured forest; noncrossing-ness corresponds to compatibility of the vertex labels with the circular order, and connectedness to the forest being a tree. Dually, each vertex of the tree becomes an $m$-gon and each $S_r$-edge a shared diagonal coloured $S_r$, which assembles an $m$-angulation; counting rooted $m$-angulations gives the Fuss-Catalan-type formula for $T_{k,m}$ (for $m = 3$, $T_{k,3} = \frac{3}{k+2}\binom{2k}{k-1}$). Since all labelled trees split evenly over the $(k-1)!$ possible $k$-cycles, $U_{k,m} = (k-1)!\,T_{k,m}$. For $m = 3$ the induction moves are the induction arising for interval exchange transformations.

## Sources

- Bethany Marsh and Sibylle Schroll, "A circular order on edge-coloured trees and RNA m-diagrams", arXiv:1010.3763 (2010), Section 2 (Lemma 2.1), Section 3 (Theorem 3.1, Corollary 3.4, Theorem 3.5, Corollaries 3.6, 3.7 and 3.9) and Section 4 (Theorem 4.11, Corollary 4.15), <https://doi.org/10.48550/arXiv.1010.3763>.
