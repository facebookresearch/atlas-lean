# Random walk on a connected regular multigraph: unique stationary law and return times

Let $G$ be a $d$-regular multigraph ($d \ge 1$) on a finite vertex set $V$ with $n$ vertices, given by a rotation map, and run the random walk that follows a uniformly random edge label at each step. Then:

(1) if $G$ is connected, the uniform distribution is its unique stationary distribution;

(2) the expected return time to $u$, $\mathbb{E}_u[\tau_u^+] \in [0, \infty]$, equals the number of vertices of the connected component of $u$; in particular it is $n$ when $G$ is connected and always at most $n \le 10 n^2$.

## Proof sketch

Regularity makes the uniform law stationary; if $\pi$ is stationary then $\pi(v)/\text{uniform}$ is a harmonic function, constant by the maximum principle. Restricting the walk to the component of $u$ and applying Kac's formula to the uniform stationary law of that component gives the return time.

## Depends on

- [Rotation map of a regular multigraph](../../graph-families-and-operations/zig-zag-product-and-explicit-expanders/rotation-map.md)

## Proof depends on

- [Maximum principle: harmonic functions on a connected regular multigraph are constant](../spectral-expansion-and-connectivity/harmonic-functions-on-regular-multigraphs-are-constant.md)

## Sources

- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
