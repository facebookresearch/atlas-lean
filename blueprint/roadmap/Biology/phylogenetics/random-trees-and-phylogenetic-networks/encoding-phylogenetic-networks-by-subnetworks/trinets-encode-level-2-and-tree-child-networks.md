# Trinets encode recoverable level-2 and tree-child networks

A *rooted phylogenetic network* on a finite set $X$ is a directed acyclic graph with a single indegree-0 vertex (the root) whose outdegree-0 vertices (leaves) are bijectively labelled by $X$; it is *binary* if all indegrees and outdegrees are at most 2 and every vertex of indegree 2 (a *reticulation*) has outdegree 1. A *cut-arc* is an arc whose deletion disconnects the underlying undirected graph; a *biconnected component* is a maximal subgraph without cut-vertices, and it is *trivial* if it is a single cut-arc. A nontrivial biconnected component is *redundant* if it has a single outgoing arc and *strongly redundant* if moreover every leaf lies below that arc; $N$ is *recoverable* if it has no strongly redundant component. $N$ is *level-$k$* if each biconnected component contains at most $k$ reticulations, and *tree-child* if every non-leaf vertex has a child that is not a reticulation.

A *trinet* is a phylogenetic network with three leaves. For $\{x,y,z\}\subseteq X$, the trinet *exhibited* by $N$ is obtained by deleting all other leaves and then repeatedly deleting unlabelled sinks and indegree-0 outdegree-1 vertices, suppressing indegree-1 outdegree-1 vertices and parallel arcs, and suppressing strongly redundant biconnected components. $Tn(N)$ is the set of all trinets exhibited by $N$, and $N$ is *encoded by its trinets* if every recoverable network $N'$ on $X$ with $Tn(N')=Tn(N)$ is isomorphic to $N$.

**Theorem.** Let $X$ be a finite set with $|X|\ge 3$.

1. Every binary, simple level-2 network on $X$ (one nontrivial biconnected component, all leaves hanging from it) is encoded by its trinets.
2. Every binary recoverable level-2 network $N$ on $X$ is encoded by $Tn(N)$.
3. Every binary tree-child network $N$ on $X$ is encoded by $Tn(N)$.
4. More generally, if $\mathcal N$ is the class of binary recoverable networks on $X$ each of whose biconnected components has at most two reticulations, or is tree-child, or has at most three outgoing cut-arcs, then every $N\in\mathcal N$ is encoded by $Tn(N)$.

**Trinet metric.** On such a class $\mathcal N$, the map

$$d(N,N') = |Tn(N)\,\Delta\,Tn(N')|$$

(the size of the symmetric difference of the trinet sets) is a metric.

## Depends on

- [Trinet decomposition of recoverable networks by cut-arc sets and biconnected components](trinet-decomposition-by-cut-arc-sets-and-biconnected-components.md)

## Expansion

By the decomposition theorem it suffices to treat single biconnected components. A simple level-$k$ network arises from a *generator* by hanging leaves on its sides; a trinet is *crucial* when it is itself a simple level-$k$ network, in which case it has the same generator. Every level-2 generator has a set of at most two crucial sides, so every simple level-2 network has a crucial trinet, and every leaf lies in one; the crucial trinets fix the generator and then the positions of the remaining leaves. For tree-child networks, each reticulation $r$ has a tree path to a leaf $x$, and when one parent of $r$ is not an ancestor of the other parent, that parent is the unique lowest common ancestor of $x$ and a leaf reached from it by a tree path; unique lowest common ancestors survive in exhibited trinets, which lets the reticulation arcs be reconstructed by induction. Encoding makes $Tn$ injective on $\mathcal N$, which is exactly what is needed for the symmetric-difference distance to separate distinct networks. The results support the conjecture that all recoverable networks are encoded by their trinets, in contrast with triplets, which encode trees but not networks.

## Sources

- Leo van Iersel, Vincent Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", Journal of Mathematical Biology 68 (2014), 1707–1729, <https://doi.org/10.1007/s00285-013-0683-5>. Published version of arXiv:1210.0362, cited next; locators there refer to the arXiv version.
- Leo van Iersel and Vincent Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", arXiv:1210.0362 (2012), Section 2 (definitions, Observations 1-4), Section 3 (Theorems 1 and 2), Section 4 (Theorem 3, Corollary 1), Section 5 (Theorem 4), Section 6 (Corollaries 2 and 3), <https://doi.org/10.48550/arXiv.1210.0362>.
