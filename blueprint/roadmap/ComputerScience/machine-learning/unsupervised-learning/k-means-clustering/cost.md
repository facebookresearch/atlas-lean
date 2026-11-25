# The k-means cost

For points $x_i$ ($i \in \iota$, a finite type) in a normed additive
commutative group, an assignment $a$ of each point $i$ to a cluster $a(i) \in \{0, \dots, k-1\}$
and centers $c_0, \dots, c_{k-1}$, the $k$-means cost is
$\sum_{i \in \iota} \lVert x_i - c_{a(i)} \rVert^2$, the sum of the squared distances from the
points to their assigned centers.
