# Bisection width and cutwidth of graphs of maximum degree 3

Let $c_3=\frac{3}{4\pi}\arccos\frac56\approx0.13982$. There is a function $r(n)=o(n)$ such that every finite simple graph $G$ with $n$ vertices and maximum degree at most $3$ satisfies

$$
\mathrm{bw}(G)\le\mathrm{cw}(G)\le c_3n+r(n).
$$

Here the *bisection width* $\mathrm{bw}(G)$ is the minimum number of edges between the two parts of a partition of $V(G)$ into parts whose sizes differ by at most one, and the *cutwidth* $\mathrm{cw}(G)$ is the minimum, over all linear orderings of $V(G)$, of the maximum over the gaps of the ordering of the number of edges joining a vertex before the gap to a vertex after it.

## Proof sketch

The main step is the pathwidth bound $\mathrm{pw}(G)\le c_3n+o(n)$ for maximum degree $3$: label the vertices by correlated Gaussians and sweep a threshold through the labels, using Sheppard's formula for the probability that an edge straddles the threshold. For maximum degree $3$, bisection width is at most cutwidth, and cutwidth is at most pathwidth plus $2$ (cutwidth equals the search number, which is at most the vertex separation number plus $2$, and vertex separation number equals pathwidth).

## Proof depends on

- [Sheppard's formula (Gaussian arcsine law)](../../Probability/distributions/continuous/multivariate-normal-distribution/sheppard-formula/sheppard-quadrant-probability-arcsine.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", arXiv:2611.05146v1, 2026, Corollary 1.2 (from Theorem 1.1(a), proved as Theorem 8.1).
