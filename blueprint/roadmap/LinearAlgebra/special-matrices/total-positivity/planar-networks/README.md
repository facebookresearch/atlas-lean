# Total nonnegativity of planar networks

Let $V$ be a set of vertices with directed edges along which some function $V \to \mathbb{N}$ strictly increases, so that the network is acyclic. Let $A_0, \dots, A_{n-1}$ (sources) and $B_0, \dots, B_{n-1}$ (sinks) be vertices such that each set $P_{ij}$ of paths from $A_i$ to $B_j$ is finite, and suppose the network is noncrossing: whenever $i < j$ and $l < k$, every path from $A_i$ to $B_k$ shares a vertex with every path from $A_j$ to $B_l$. Let the edges carry nonnegative weights in an ordered commutative ring, and let the weight of a path be the product of the weights of its edges. Then the weight matrix $M_{ij} = \sum_{p \in P_{ij}} w(p)$ is totally nonnegative.

## Idea

By the Lindström–Gessel–Viennot lemma, each minor of the weight matrix counts, with signs, families of paths from some sources to some sinks; in a noncrossing network only vertex-disjoint families that connect the sources to the sinks in order survive, and they all come with a plus sign. So nonnegative weights give nonnegative minors, and positive weights on a suitably connected network give positive minors. Conversely, every totally positive matrix is the weight matrix of such a planar network with positive weights, a fact going back to Loewner and Whitney that Fomin and Zelevinsky use to obtain parametrizations and efficient tests of total positivity.

## Statements

- [Total nonnegativity of planar networks](planar-network-is-totally-nonneg.md)
- [Total positivity of totally connected planar networks](planar-network-has-positive-minors.md): a stronger form: totally connected networks with positive weights give totally positive matrices
- [Nonnegative edge weights give nonnegative path weights](lgv-path-weight-nonneg.md): nonnegative edge weights give nonnegative path weights
- [Positive edge weights give positive path weights](lgv-path-weight-pos.md): positive edge weights give positive path weights
