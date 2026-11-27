# q-cuttable networks and tree-child orientations

An *unrooted binary phylogenetic network* $U$ on a finite taxon set $X$ is a simple connected undirected graph whose internal vertices have degree $3$ and whose degree-$1$ vertices (leaves) are bijectively labeled by $X$. An edge is a *cut-edge* if deleting it disconnects $U$; a *blob* is a maximal subgraph without cut-edges that is not a single vertex. An *orientation* of $U$ subdivides one edge by a new root $\rho$ and directs every edge; $U$ is *tree-child* if some orientation is a rooted tree-child network (every non-leaf vertex has a child that is a tree vertex or a leaf; equivalently, no reticulation has a reticulation parent and no two reticulations are siblings).

**Hardness.** The problem of deciding whether an unrooted phylogenetic network has a tree-child orientation is NP-complete (by reduction from a balanced 3-SAT variant in which each literal occurs exactly twice).

**$q$-cuttable networks.** For an integer $q\ge1$, $U$ is *$q$-cuttable* if every cycle of $U$ contains a path of at least $q$ vertices each incident to a cut-edge. A *chain* is a path of vertices in one blob, all incident to cut-edges; its length is its number of vertices. The following are equivalent:

1. $U$ is $q$-cuttable, i.e., every cycle contains a chain of length $q$;
2. deleting every vertex that lies in a length-$q$ chain leaves a forest;
3. deleting an arbitrary edge from each maximal chain of length at least $q$ leaves a forest.

Hence $q$-cuttability can be recognized in polynomial time.

**Properties.** Let $U$ be $2$-cuttable on $X$. Then

- $U$ has a tree-child orientation;
- $U$ is an orchard network;
- the number of reticulations $r(U)=|E|-(|V|-1)$ satisfies $r(U)\le|X|-1$.

For every $k\ge0$ and $q\ge1$ there is a $q$-cuttable network that is strictly level-$k$, so the classes are not contained in any bounded-level class.

## Expansion

For a $2$-cuttable network, deleting a suitable set $S'$ of chain edges leaves a spanning tree with leaf set $X$. Placing the root on a cut-edge and directing all tree edges away from it fixes most of the orientation. In each blob, the deleted chain edges are grouped through an auxiliary multigraph of maximum degree $2$ (so its components are paths and cycles), and the edges of each component are oriented consistently along one path through the blob. The heads of these arcs become the reticulations; the structure of chains rules out stacked or sibling reticulations, and the fact that each blob has a unique entry vertex rules out directed cycles. The resulting rooted network is tree-child, which also gives the orchard property and the rooted tree-child bound of at most $|X|-1$ reticulations.

## Sources

- L. van Iersel, M. Jones, S. Linz and N. Zeh, "A Class of Unrooted Phylogenetic Networks Inspired by the Properties of Rooted Tree-Child Networks", *Discrete Applied Mathematics* 398 (2027), 76–96, Lemma 1, Theorem 4, Definition 1, Observation 5, Theorem 6, Proposition 7, Corollaries 8-9 and Observation 10, <https://doi.org/10.1016/j.dam.2026.10.022> (preprint arXiv:2603.07000).
