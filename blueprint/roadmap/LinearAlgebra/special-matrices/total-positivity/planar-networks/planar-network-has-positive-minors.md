# Total positivity of totally connected planar networks

Let $V$ be a set of vertices and $E$ a set of directed edges on $V$, and suppose that
some function $\mathrm{rank} : V \to \mathbb{N}$ strictly increases along every edge, so that the
network is acyclic. Let $A_0, \dots, A_{n-1}$ (sources) and $B_0, \dots, B_{n-1}$ (sinks) be
vertices. A path from $u$ to $v$ is a list of vertices that starts at $u$, ends at $v$ and follows
edges; for all $i, j$ the set $P_{ij}$ of all paths from $A_i$ to $B_j$ is assumed to be finite.
Suppose the network is noncrossing: whenever $i < j$ and $l < k$, every path from $A_i$ to $B_k$
shares a vertex with every path from $A_j$ to $B_l$.
Let $w(u, v) > 0$ be real edge weights, let the weight of a path be the product of the weights of
its consecutive edges, and let $M_{ij} = \sum_{p \in P_{ij}} w(p)$. Suppose moreover that the network
is totally connected: for all row indices $r_0 < \dots < r_{k-1}$ and column indices
$c_0 < \dots < c_{k-1}$ there are pairwise vertex-disjoint paths from $A_{r_a}$ to $B_{c_a}$,
$0 \le a < k$. Then every minor of $M$ is positive (Fomin and Zelevinsky, *Total positivity: tests
and parametrizations*, Math. Intelligencer 22 (2000), no. 1, 23–33, arXiv:math/9912128v1,
Corollary 3).

## Background

- [Total nonnegativity of planar networks](planar-network-is-totally-nonneg.md): the same argument with nonnegative weights; total connectedness makes every sum nonempty, hence positive.
- [Gasca–Peña criterion for total positivity](../totally-positive-matrices/has-positive-minors-iff-initial-minors-p.md): the test of total positivity by the $n^2$ initial minors (Fomin–Zelevinsky, Theorem 9), which they derive from the converse parametrisation of totally positive matrices by planar networks.
