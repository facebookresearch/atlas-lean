# The cost as a sum over clusters

For points $x_i$ ($i \in \iota$, a finite type) in a
normed additive commutative group, an assignment $a$ of each point $i$ to a cluster
$a(i) \in \{0, \dots, k-1\}$ and centers $c_0, \dots, c_{k-1}$, the $k$-means cost equals
$\sum_{j} \sum_{i : a(i) = j} \lVert x_i - c_j \rVert^2$: for each cluster $j$, add up the squared
distances from the points assigned to $j$ to its center $c_j$.
