# Total nonnegativity of planar networks

Let $V$ be a set of vertices and $E$ a set of directed edges on $V$, and suppose that
some function $\mathrm{rank} : V \to \mathbb{N}$ strictly increases along every edge, so that the
network is acyclic. Let $A_0, \dots, A_{n-1}$ (sources) and $B_0, \dots, B_{n-1}$ (sinks) be
vertices. A path from $u$ to $v$ is a list of vertices that starts at $u$, ends at $v$ and follows
edges; for all $i, j$ the set $P_{ij}$ of all paths from $A_i$ to $B_j$ is assumed to be finite.
Suppose the network is noncrossing: whenever $i < j$ and $l < k$, every path from $A_i$ to $B_k$
shares a vertex with every path from $A_j$ to $B_l$.
Let $w(u, v) \ge 0$ be edge weights in an ordered commutative ring, and let the weight of a path be
the product of the weights of its consecutive edges. Then the weight matrix

$$M_{ij} = \sum_{p \in P_{ij}} w(p)$$

is totally nonnegative: all its minors are $\ge 0$ (Fomin and Zelevinsky, *Total positivity: tests
and parametrizations*, Math. Intelligencer 22 (2000), no. 1, 23–33, arXiv:math/9912128v1,
Corollary 2, from Lemma 1).

The sums must run over all paths from $A_i$ to $B_j$; with an arbitrary subset of paths the minors
can be negative. The noncrossing condition holds for the planar networks of the source, whose
sources and sinks lie on the boundary in the same order; it is the only consequence of planarity
that the proof uses.

## Background

- [Weighted Lindström–Gessel–Viennot lemma, noncrossing form](../../../Combinatorics/catalan-numbers-lattice-paths/dyck-paths-lattice-walks/lindstrom-gessel-viennot-weighted.md): applied to each minor, it writes the minor as a sum of weights of vertex-disjoint path families.
- [Cluster algebras](../../../RingTheory/cluster-algebras/README.md): Fomin and Zelevinsky introduced cluster algebras to explain the combinatorics of such positivity tests (double wiring diagrams and their mutations).
