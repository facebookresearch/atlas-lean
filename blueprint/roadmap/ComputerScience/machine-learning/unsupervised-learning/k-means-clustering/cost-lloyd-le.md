# One round of Lloyd's algorithm never increases the cost

Let $x_i$ ($i \in \iota$, a finite type) be points in a real inner product space, $a$ an
assignment of the points to clusters $0, \dots, k - 1$ and $c$ any centers. Recompute the centers
as the [centroids](centers.md) $c'$ of the clusters of $a$, then reassign every point to a
nearest center of $c'$, giving $a'$. Then the [$k$-means cost](cost.md) of $(a', c')$ is at most
that of $(a, c)$.
