# The update step never increases the cost

Let $x_i$ ($i \in \iota$, a finite type) be points in a real inner product space and $a$ an
assignment of the points to clusters $0, \dots, k - 1$. For a fixed assignment the
[centroids](centers.md) are the best centers: for all centers $c_0, \dots, c_{k-1}$, the
[$k$-means cost](cost.md) of $a$ with the centroids of its clusters is at most the cost of $a$
with $c$.
