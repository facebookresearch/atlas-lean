# Coordinate shift between grid cubes

Let $n$ and $d$ be natural numbers, let
$\sigma$ be a permutation of the index set $\{0, \dots, n-1\}^d$, let $k$ be an index and
let $i < d$. The shift along axis $i$ determined by $\sigma$ and $k$ is the point
$(\sigma(k)_i - k_i)/n$ of the circle $\mathbb{R}/\mathbb{Z}$, that is, the class modulo $1$
of this real number.

For an index $j$, the grid cube with index $j$ is the set of points of the torus
$(\mathbb{R}/\mathbb{Z})^d$ whose $m$-th coordinate is the class of a real number in
$[j_m/n, (j_m + 1)/n)$ for every $m < d$. For $n > 0$, translating the $m$-th coordinate of
each point of the grid cube with index $k$ by the shift along axis $m$, for every $m < d$,
carries that cube onto the grid cube with index $\sigma(k)$.
