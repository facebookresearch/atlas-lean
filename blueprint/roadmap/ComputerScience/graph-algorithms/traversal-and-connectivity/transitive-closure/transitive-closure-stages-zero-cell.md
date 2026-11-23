# Initial matrix of the transitive-closure computation

Let $A$ be a Boolean adjacency
matrix on the vertices $0, \dots, n-1$. For all vertices $i$ and $j$, the entry $(i, j)$ of the
matrix produced by the staged transitive-closure computation with no pivot stages is true if and
only if $i = j$ or $A_{ij}$ is true.
