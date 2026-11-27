# Spectral expansion, second eigenvalue and edge expansion of a regular multigraph

Let $G$ be a $D$-regular multigraph on a finite vertex set $V$, $|V| = N$, presented by a rotation map on $V \times L$ with $|L| = D \ge 1$; write $v[i]$ for the far endpoint of the edge labelled $i$ at $v$. The walk operator is $(W_G f)(v) = \frac1D \sum_{i \in L} f(v[i])$ on functions $f : V \to \mathbb{R}$; it is self-adjoint for $\langle f, g \rangle = \mathbb{E}_v f(v) g(v)$ and fixes constants.

The spectral expansion $\lambda(G) \ge 0$ is the least $c$ with $\mathbb{E}_v (W_G f)(v)^2 \le c^2\, \mathbb{E}_v f(v)^2$ for every $f$ with $\mathbb{E}_v f = 0$; it is the largest absolute value of an eigenvalue of $W_G$ on the mean-zero functions. The second eigenvalue $\lambda_2(G)$ is the supremum of $\mathbb{E}_v f\, W_G f / \mathbb{E}_v f^2$ over nonzero mean-zero $f$, so $-\lambda(G) \le \lambda_2(G) \le \lambda(G)$. The edge expansion is

$$h(G) = \min_{\emptyset \ne S \subseteq V,\ |S| \le N/2} \frac{e(S, V \setminus S)}{|S|},$$

where $e(S, V\setminus S)$ counts the darts $(v, i)$ with $v \in S$ and $v[i] \notin S$. Both $\lambda_2$ and $h$ are $0$ when $N \le 1$.

## Depends on

- [Rotation map of a regular multigraph](../zig-zag-product-and-explicit-expanders/rotation-map.md)
- [$(N, D, \lambda)$-graph given by a rotation map](../zig-zag-product-and-explicit-expanders/is-ndlambda-graph.md)

## Sources

- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002.
