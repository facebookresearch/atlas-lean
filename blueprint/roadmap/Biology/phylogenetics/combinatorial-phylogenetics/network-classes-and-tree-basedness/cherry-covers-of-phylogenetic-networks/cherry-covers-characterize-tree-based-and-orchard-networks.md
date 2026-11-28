# Cherry covers characterize tree-based and orchard networks

**Shapes.** In a rooted phylogenetic network (a rooted DAG with labelled leaves, tree vertices and reticulations), a *cherry shape* is a pair of edges $p\to x$, $p\to y$ leaving a common vertex $p$; a *reticulated cherry shape* is a path $x\leftarrow p_x\leftarrow p_y\to y$ of three edges whose middle edge $p_y\to p_x$ enters a reticulation $p_x$. In both, $x$ and $y$ are the *endpoints* and the other vertices are *internal*. For a network $N$, the *bulged version* $B(N)$ replaces the outgoing edge of each reticulation of indegree $k$ by $k-1$ parallel edges.

A *cherry cover* of $B(N)$ is a set $P$ of cherry shapes and reticulated cherry shapes such that every edge other than the root edge is covered by at least one shape, every outgoing edge of a reticulation is covered exactly once, and every edge covered by the middle edge of a reticulated cherry shape is covered exactly once. (For binary networks this means every non-root edge is covered exactly once: a *cherry decomposition*.) Shape $A$ is *directly above* shape $B$ if an internal vertex of $B$ is an endpoint of $A$; $P$ is *acyclic* if the transitive closure of this relation has no cycle.

**Counting lemma.** In a binary network with $n$ leaves and $r$ reticulations, every cherry decomposition has exactly $n-1$ cherry shapes and $r$ reticulated cherry shapes. A network has a cherry cover using only cherry shapes iff it is a tree.

**Theorem (tree-based networks).** A network $N$ is tree-based with base tree $T$ if it is obtained from $T$ by (1) replacing some edges of $T$ by paths whose internal vertices (*attachment points*) have in-degree and out-degree $1$, (2) adding *linking arcs* between pairs of attachment points and from tree vertices to attachment points, so that $N$ stays acyclic, every attachment point has in-degree $1$ or out-degree $1$, and $N$ has no parallel arcs, and (3) suppressing every attachment point not incident to a linking arc (the source's Definition 7). $N$ is tree-based if and only if $B(N)$ has a cherry cover.

**Theorem (orchard networks).** A network $N$ is orchard (reducible to a single leaf by a sequence of cherry and reticulated-cherry reductions) if and only if $B(N)$ has an acyclic cherry cover.

**Corollary.** Every orchard network is tree-based; both properties hold for $N$ iff they hold for some binary (or semi-binary) resolution of $N$.

## Expansion

Given a base tree, each tree edge pair at a split gives a cherry shape and each linking arc, together with the tree edges at its ends, gives a reticulated cherry shape; conversely the cherry shapes of a cover glue into a spanning tree whose complementary middle edges are linking arcs. For orchard networks, a lowest shape in an acyclic cover has leaf endpoints and is exactly a reducible pair (cherry or reticulated cherry); reducing it leaves an acyclic cover of the smaller network, so induction over a linear extension of the "above" order produces a full cherry-picking sequence, and the converse records each reduction as a shape. Acyclicity is what separates orchard from merely tree-based networks.

## Sources

- Leo van Iersel, Remie Janssen, Mark Jones, Yukihiro Murakami and Norbert Zeh, "A Unifying Characterization of Tree-based Networks and Orchard Networks using Cherry Covers", arXiv:2004.07677: Definitions 1–5 and 7, Lemmas 1, 2 and 4 (counting), Theorem 1 and Corollary 1 (tree-based), Lemma 6 and Theorem 2 (orchard), Lemmas 5 and 7 and Corollary 2 (resolutions, orchard implies tree-based). <https://doi.org/10.48550/arXiv.2004.07677> Published version: Advances in Applied Mathematics 129 (2021) 102222, <https://doi.org/10.1016/j.aam.2021.102222>.
