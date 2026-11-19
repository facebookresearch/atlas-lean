# Quadtree difference is pointwise set difference at sufficient scale

Let $s$ and $t$ be Boolean region quadtrees and $n, i, j \in \mathbb{N}$, with the heights of $s$
and $t$ both at most $n$. Then the lookup of the cell $(i, j)$ at scale $n$ in $s \setminus t$ is
true exactly when the lookup of $(i, j)$ at scale $n$ is true in $s$ and false in $t$.
