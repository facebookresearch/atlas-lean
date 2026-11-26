# Visit counts of random walks on connected regular multigraphs concentrate around t/n

Let $G$ be a connected $d$-regular multigraph on $n$ vertices, given by a rotation map, and for a label sequence $k \in L^t$ let $\mathrm{vis}_{u,v}(k)$ be the number of times $i \in \{1, \dots, t\}$ at which the walk from $u$ along $k$ is at $v$. For all $u, v$ and every $\varepsilon > 0$ there is $T$ such that for all $t \ge T$, at least a $(1 - \varepsilon)$ fraction of the $d^t$ label sequences satisfy

$$\frac{(1 - \varepsilon)\, t}{n} \le \mathrm{vis}_{u,v}(k) \le \frac{(1 + \varepsilon)\, t}{n}.$$

No aperiodicity is assumed; no explicit rate is given.

## Proof sketch

By the maximum principle the fixed vectors of the walk operator are the constants, so von Neumann's mean ergodic theorem makes the Cesaro averages of $W^j(1_v - 1/n)$ tend to $0$ uniformly in the start. A first-step recursion for the second moment of $S_t = \mathrm{vis} - t/n$ then gives $\mathbb{E} S_t^2 = o(t^2)$, and Chebyshev's inequality concludes. Equivalently, the walk along uniform labels is an irreducible Markov chain whose stationary law is uniform (the rotation map is a bijection), so the ergodic theorem gives $\mathrm{vis}_{u,v}/t \to 1/n$ almost surely, hence in probability.

## Depends on

- [Rotation map of a regular multigraph](../../graph-families-and-operations/zig-zag-product-and-explicit-expanders/rotation-map.md)

## Proof depends on

- [Maximum principle: harmonic functions on a connected regular multigraph are constant](../spectral-expansion-and-connectivity/harmonic-functions-on-regular-multigraphs-are-constant.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017, Appendix C, Theorem C.1 (Ergodic Theorem).
