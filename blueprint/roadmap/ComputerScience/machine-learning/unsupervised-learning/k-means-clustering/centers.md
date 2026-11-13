# The centroid update step

Let $x_i$ ($i \in \iota$, a finite type) be points in a real
inner product space and let $a$ assign each point $i$ to a cluster $a(i) \in \{0, \dots, k-1\}$.
The updated centers send each cluster $j$ to the centroid of the points $x_i$ with $a(i) = j$.
A cluster with no points gets the center $0$, which does not affect the $k$-means cost of $a$.
