# Quadtree union is pointwise disjunction at sufficient scale

Let $s$ and $t$ be Boolean region quadtrees and $n, i, j \in \mathbb{N}$, with the heights of $s$
and $t$ both at most $n$. Then the lookup of the cell $(i, j)$ at scale $n$ in $s \cup t$ is true
exactly when the lookup of $(i, j)$ at scale $n$ in $s$ or in $t$ is true.
