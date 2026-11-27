# Powers of a regular multigraph: the spectral expansion is multiplicative

For a $D$-regular multigraph $G$ given by a rotation map on $V \times L$ and $t \ge 1$, the $t$-th power $G^t$ is the $D^t$-regular multigraph on $V$ with one edge, labelled $(i_1, \dots, i_t) \in L^t$, for every walk of length $t$ along those labels, its rotation map reversing the walk. Its walk operator is $W_G^t$ and

$$\lambda(G^t) = \lambda(G)^t,$$

where $\lambda$ is the spectral expansion (operator norm of the walk operator on mean-zero functions under the uniform measure).

## Proof sketch

The inequality $\lambda(G^t) \le \lambda(G)^t$ holds for any operator norm since $W_{G^t} = W_G^t$ preserves the mean-zero space. For the reverse inequality, self-adjointness makes the second moments $a_s = \mathbb{E}(W_G^s f)^2$ log-convex in $s$, giving $a_0 a_1^t \le a_0^t a_t$; choosing $f$ nearly extremal for $\lambda(G)$ yields $\lambda(G^t) \ge \lambda(G)^t$.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)
- [Square of a rotation map](../zig-zag-product-and-explicit-expanders/square.md)

## Proof depends on

- [Squaring squares the spectral parameter](../zig-zag-product-and-explicit-expanders/is-ndlambda-graph-square.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
