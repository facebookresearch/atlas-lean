# Restricted tree of a phylogenetic network and its universality

Let $N=(V,A,r,X)$ and $N'=(V',A',r',X)$ be $X$-networks (rooted directed graphs whose leaves are identified with the finite set $X$ and in which every vertex is ancestral to a leaf). An **$X$-digraph map** $f: N \to N'$ is a map $V \to V'$ with $f(r) = r'$, $f(x) = x$ for $x \in X$, and such that every arc $(u,v)$ of $N$ has either $f(u) = f(v)$ or $(f(u), f(v)) \in A'$. It is a **CSD map** (connected surjective digraph map) if every fiber $f^{-1}(v')$ is nonempty and connected in the underlying undirected graph of $N$, and every arc of $N'$ is the image of an arc of $N$. A CSD map is **restricted** if every fiber is a restricted set (a set entered from at most one outside vertex; see the dependency).

For an acyclic $X$-network $N$, let $R(v)$ be the smallest restricted set containing $v$, call $R(v)$ and $R(w)$ related when they intersect, and let $R'(v)$ be the union of all $R(w)$ in the equivalence class of $R(v)$ under the transitive closure of this relation. The sets $R'(v)$ partition $V$, and each is restricted and connected (Lemma 3.9). The **restricted tree** $\mathrm{ResTr}(N)$ is the quotient digraph $N/\{R'(v)\}$ (one vertex per class, an arc between distinct classes when some arc of $N$ joins them), with natural projection $\phi(v) = R'(v)$. Assume every leaf of $N$ has indegree 1. Then:

1. $\mathrm{ResTr}(N)$ is an $X$-network and $\phi: N \to \mathrm{ResTr}(N)$ is a restricted CSD map (Theorem 3.10).
2. If $f: N \to T$ is any restricted CSD map onto an $X$-network $T$, then $T$ has no vertex of indegree at least 2, so $T$ is an $X$-tree (Theorem 4.1). In particular $\mathrm{ResTr}(N)$ is an $X$-tree (Corollary 4.2).
3. There is a wired lift of $\mathrm{ResTr}(N)$ into $N$: a subgraph of the undirected graph of $N$ that contains, for each arc of $\mathrm{ResTr}(N)$, exactly one arc of $N$ mapping onto it, joined inside each fiber by a tree, so that $\mathrm{ResTr}(N)$ embeds in $N$ as an undirected network up to resolution (Corollary 4.3).
4. A composition of restricted CSD maps is a restricted CSD map (Theorem 4.5).
5. Universality: for every restricted CSD map $g: N \to T$, the kernel partition $\{R'(v)\}$ of $\phi$ refines the kernel partition of $g$, and $g = h \circ \phi$ for a CSD map $h: \mathrm{ResTr}(N) \to T$ (Theorem 4.6).

## Depends on

- [Restricted sets and the smallest restricted set of a vertex](restricted-sets-and-the-smallest-restricted-set-of-a-vertex.md)

## Expansion

The construction gives a canonical species-tree-like summary of a network with hybridization: regions of reticulation that are entered through a single ancestor are collapsed to single vertices, while tree-like parts (vertices of indegree 1 have singleton restricted sets) survive. A hybrid vertex in the image would receive arcs from two distinct fibers, but both arcs would enter the same restricted fiber from outside, so their tails equal its unique anchor; hence the image has no hybrids. Universality follows because every fiber of a restricted map is a restricted set, hence contains $R(v)$ for each of its vertices, and overlapping $R(v)$ must lie in the same fiber; the factorization then comes from the general fact that a CSD map factors through any quotient by a finer partition into connected classes. The resolution of the tree depends on the outdegrees of hybrid vertices: in the paper's example a hybrid of outdegree 1 collapses a cluster that a hybrid of outdegree 2 preserves.

## Sources

- Stephen J. Willson, Restricted trees: simplifying networks with bottlenecks, arXiv:1005.4956 (2010). <https://doi.org/10.48550/arXiv.1005.4956>. Published version: Bulletin of Mathematical Biology 73(10) (2011), 2322–2338, <https://doi.org/10.1007/s11538-010-9624-2>; locators above refer to the arXiv version.
