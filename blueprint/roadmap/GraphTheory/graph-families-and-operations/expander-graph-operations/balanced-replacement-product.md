# Balanced replacement product of rotation maps

Let $G$ be a $D$-regular multigraph with rotation map on $V \times K$ ($|K| = D$) and $H$ a $d$-regular multigraph with rotation map on $K \times L$ ($|L| = d$), so the vertices of $H$ are the edge labels of $G$. The balanced replacement product $G \circledR H$ is the $2d$-regular multigraph on $V \times K$ with labels $L \sqcup L$: a label in the first copy of $L$ moves inside the cloud $\{v\} \times K$ along the corresponding edge of $H$, and a label in the second copy follows the edge of $G$, $(v, k) \mapsto \mathrm{rot}_G(v, k)$ (each such edge repeated $d$ times). Its walk operator is $\frac12(\tilde B + \tilde A)$, where $\tilde B$ applies $W_H$ in every cloud and $\tilde A$ is the permutation of $V \times K$ given by $\mathrm{rot}_G$.

## Depends on

- [Rotation map of a regular multigraph](../zig-zag-product-and-explicit-expanders/rotation-map.md)
- [Zig-zag product of rotation maps](../zig-zag-product-and-explicit-expanders/zigzag.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
