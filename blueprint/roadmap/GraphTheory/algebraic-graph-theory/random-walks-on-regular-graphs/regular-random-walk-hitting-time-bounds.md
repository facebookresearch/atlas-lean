# Hitting times and miss probabilities of random walks on regular multigraphs

Let $G$ be a $d$-regular multigraph on $n$ vertices, given by a rotation map, with $d \le n$, and run the random walk along uniformly random labels. If $u$ and $v$ are joined by a path of length at most $k$, then the expected hitting time satisfies $\mathbb{E}_u[\tau_v] \le 100\, k\, n^2$. Consequently, if $s$ and $t$ are connected, at most a tenth of the $d^{1000 n^3}$ label sequences of length $1000 n^3$ give a walk from $s$ that never visits $t$.

## Proof sketch

Bound the hitting time across one edge: the return time to $v$ is $n$ (component size at most $n$), and decomposing it by the first step shows the hitting time from any neighbour is at most $d\cdot n \le n^2$ up to constants; summing along the path gives $100kn^2$. Markov's inequality with $k \le n$ gives the miss probability.

## Depends on

- [Rotation map of a regular multigraph](../../graph-families-and-operations/zig-zag-product-and-explicit-expanders/rotation-map.md)

## Proof depends on

- [Random walk on a connected regular multigraph: unique stationary law and return times](regular-random-walk-stationary-law-and-return-times.md)

## Sources

- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
