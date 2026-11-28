# Karger-Motwani-Sudan coloring of 3-colorable graphs by rounding vector colorings

There is a randomized polynomial-time algorithm that, given a $3$-colorable graph $G$ with $n$ vertices and maximum degree $\Delta$, outputs with high probability a proper coloring with

$$
\min\left\{ O\!\left(\Delta^{1/3} \log^{1/2} \Delta \, \log n\right),\; O\!\left(n^{1/4} \log^{1/2} n\right) \right\}
$$

colors. More generally, a $k$-colorable graph is colored with $\min\{ O(\Delta^{1 - 2/k} \log^{1/2} \Delta \log n), O(n^{1 - 3/(k + 1)} \log^{1/2} n) \}$ colors. The algorithm uses only a vector $k$-coloring, and a vector $(k + \varepsilon)$-coloring of a vector $k$-colorable graph can be computed in time polynomial in $n$ and $\log(1/\varepsilon)$.

## Proof sketch

Solve the semidefinite program for a vector $(k + \varepsilon)$-coloring. Pick a standard Gaussian vector $r$ and keep the vertices $v$ with $\langle u_v, r \rangle \ge c$ for a threshold $c$ chosen from Gaussian tail estimates; since adjacent vectors are far apart, the expected number of edges inside the kept set is a small fraction of its expected size, and deleting one endpoint of each such edge leaves an independent set of size $\Omega(n / (\Delta^{1 - 2/k} \sqrt{\log \Delta}))$. Repeating on the remaining graph colors everything with the degree-based bound times $O(\log n)$ colors; the $n$-based bound follows from Wigderson's trick: the neighbourhood of a vertex of degree above $n^{k/(k+1)}$ is vector $(k-1)$-colorable ($2$-colorable when $k = 3$), so it yields a large independent set by induction on $k$, and otherwise the degree bound applies.

## Depends on

- [Vector colorings and the vector chromatic number](vector-colorings-and-vector-chromatic-number.md)

## Proof depends on

- [A random hyperplane separates two unit vectors with probability angle over π](../../../Probability/distributions/continuous/multivariate-normal-distribution/sheppard-formula/std-gaussian-sign-ne.md)

## Sources

- D. Karger, R. Motwani, M. Sudan, "Approximate Graph Coloring by Semidefinite Programming", Journal of the ACM 45 (1998), arXiv:cs/9812008.
