# Quadtree complementation negates lookup at sufficient scale

Let $t$ be a Boolean region quadtree and $n, i, j \in \mathbb{N}$ with the height of $t$ at most
$n$. Then the lookup of the cell $(i, j)$ at scale $n$ in the complement of $t$ is the negation
of the lookup of $(i, j)$ at scale $n$ in $t$.
