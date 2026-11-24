# Simplicial boundary matrix

For a finite family $K$ of finite subsets of $\mathbb{N}$ and
$k \in \mathbb{N}$, the boundary matrix $\partial_k$ of $K$ is the matrix over $\mathbb{Q}$ whose
rows are indexed by the faces of $K$ with $k$ vertices and whose columns are indexed by the faces
of $K$ with $k + 1$ vertices; its entry at $(\tau, \sigma)$ is $(-1)^i$ when $\tau$ is obtained
from $\sigma$ by removing its $i$-th smallest vertex, counting from $i = 0$, and $0$ otherwise.

It represents the boundary map from the faces with $k + 1$ vertices to the faces with $k$
vertices. For $k = 0$ it is the augmentation: every vertex has entry $1$ in the row of the empty
face.
