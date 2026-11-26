# Node and edge counts of tree-child networks

A *rooted binary phylogenetic network* on a taxon set of size $n$ is a directed acyclic graph with a root of indegree $0$ and outdegree $1$, *tree nodes* of indegree $1$ and outdegree $2$, *reticulation nodes* of indegree $2$ and outdegree $1$, and $n$ leaves of indegree $1$ bijectively labeled by the taxa. It is *tree-child* if every non-leaf node has a child that is a tree node or a leaf. A tree node is *free* if neither of its children is a reticulation; an edge entering a tree node or a leaf is a *tree edge*.

**Proposition.** A tree-child network $N$ with $k$ reticulations on $n$ taxa has exactly

- $n+k-1$ tree nodes,
- $n-k-1$ free tree nodes, and
- $2n+k-1$ tree edges,

and therefore $0\le k<n$.

## Expansion

Counting edges by tail and by head gives $1+2t+k=t+2k+n$ for $t$ tree nodes, so $t=n+k-1$. Each reticulation has two distinct tree-node parents, and by the tree-child property a tree node has at most one reticulation child, so exactly $2k$ tree nodes are not free and $t-2k=n-k-1$ are free. Every tree node and leaf has exactly one incoming edge, giving $2n+k-1$ tree edges. Nonnegativity of the number of free tree nodes gives $k\le n-1$.

## Sources

- H. Yu and L. Zhang, "A Short Combinatorial Proof of the Pons-Batle Identity for Counting Tree-Child Networks", arXiv preprint (2026), <https://doi.org/10.48550/arXiv.2609.04979>. Proposition 2.1.
