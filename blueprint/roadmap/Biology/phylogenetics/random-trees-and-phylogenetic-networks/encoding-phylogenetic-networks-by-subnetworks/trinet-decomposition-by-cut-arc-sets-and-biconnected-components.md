# Trinet decomposition of recoverable networks by cut-arc sets and biconnected components

A *rooted phylogenetic network* on a finite set $X$ is a directed acyclic graph with a single indegree-0 vertex (the root) whose outdegree-0 vertices (leaves) are bijectively labelled by $X$; it is *binary* if all indegrees and outdegrees are at most 2 and every vertex of indegree 2 (a *reticulation*) has outdegree 1. A *cut-arc* is an arc whose deletion disconnects the underlying undirected graph; a *biconnected component* is a maximal subgraph without cut-vertices, and it is *trivial* if it is a single cut-arc. A nontrivial biconnected component is *redundant* if it has a single outgoing arc and *strongly redundant* if moreover every leaf lies below that arc; $N$ is *recoverable* if it has no strongly redundant component. $N$ is *level-$k$* if each biconnected component contains at most $k$ reticulations, and *tree-child* if every non-leaf vertex has a child that is not a reticulation.

A *trinet* is a phylogenetic network with three leaves. For $\{x,y,z\}\subseteq X$, the trinet *exhibited* by $N$ is obtained by deleting all other leaves and then repeatedly deleting unlabelled sinks and indegree-0 outdegree-1 vertices, suppressing indegree-1 outdegree-1 vertices and parallel arcs, and suppressing strongly redundant biconnected components. $Tn(N)$ is the set of all trinets exhibited by $N$, and $N$ is *encoded by its trinets* if every recoverable network $N'$ on $X$ with $Tn(N')=Tn(N)$ is isomorphic to $N$.

A set $A\subseteq X$ is a *CA-set* (cut-arc set) of $N$ if there is a cut-arc $(u,v)$ such that $A$ is exactly the set of leaves below $v$.

**Theorem (CA-sets are visible in trinets).** Let $N$ be a recoverable binary phylogenetic network on $X$ and $A\subset X$. Then $A$ is a CA-set of $N$ if and only if $|A|=1$, or for all $z\in X\setminus A$ and all distinct $x,y\in A$, the pair $\{x,y\}$ is a CA-set of the trinet on $\{x,y,z\}$ exhibited by $N$.

**Theorem (reduction to biconnected components).** A recoverable binary phylogenetic network $N$ on $X$ with $|X|\ge 3$ is encoded by $Tn(N)$ if and only if, for every nontrivial biconnected component $B$ of $N$ with at least four outgoing cut-arcs, the restriction $N_B$ is encoded by $Tn(N_B)$. Here, if $a_1=(u_1,v_1),\ldots,a_b=(u_b,v_b)$ are the outgoing cut-arcs of $B$, the *restriction* $N_B$ is obtained from $N$ by deleting all biconnected components except $B,a_1,\ldots,a_b$ and labelling $v_1,\ldots,v_b$ by new leaf labels.

## Expansion

If $(u,v)$ is a cut-arc of $N$, its leaf set meets every exhibited trinet in a CA-set, because the trinet construction never destroys the cut. Conversely, in a recoverable binary network without redundant components, CA-sets correspond bijectively to cut-arcs, and the three-leaf test reconstructs every cut-arc from trinets alone. Knowing all cut-arcs recovers the tree-like skeleton of $N$ (its tree of biconnected components), so encoding reduces to the individual blobs. A component with at most three outgoing cut-arcs has a restriction with at most three leaves, which is itself a trinet, so only components with four or more outgoing cut-arcs need an argument. These two theorems are the engine behind the encoding of level-2 and tree-child networks.

## Sources

- Leo van Iersel, Vincent Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", Journal of Mathematical Biology 68 (2014), 1707–1729, <https://doi.org/10.1007/s00285-013-0683-5>. Published version of arXiv:1210.0362, cited next; locators there refer to the arXiv version.
- Leo van Iersel and Vincent Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", arXiv:1210.0362 (2012), Section 2 (definitions, Observations 1-4), Section 3 (Theorems 1 and 2), Section 4 (Theorem 3, Corollary 1), Section 5 (Theorem 4), Section 6 (Corollaries 2 and 3), <https://doi.org/10.48550/arXiv.1210.0362>.
