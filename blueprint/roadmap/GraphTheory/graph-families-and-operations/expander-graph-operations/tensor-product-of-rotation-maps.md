# Spectral expansion of the tensor product of rotation maps

Let $G$ be a $D$-regular multigraph on $V$ (rotation map on $V \times L$) and $H$ a $D'$-regular multigraph on $V'$ (rotation map on $V' \times L'$). The tensor product $G \otimes H$ is the $DD'$-regular multigraph on $V \times V'$ whose rotation map sends $((v, v'), (i, i'))$ to $((w, w'), (j, j'))$ where $(w, j) = \mathrm{rot}_G(v, i)$ and $(w', j') = \mathrm{rot}_H(v', i')$: one step in each factor simultaneously. Then

$$\lambda(G \otimes H) \le \max\{\lambda(G), \lambda(H)\},$$

with equality when both factors have nonempty vertex and label sets; here $\lambda$ is the spectral expansion.

## Proof sketch

The walk operator factors as $(W_G \otimes I)(I \otimes W_H)$. Split a function of mean zero on $V \times V'$ into its averages over the fibres $\{v\} \times V'$ (a mean-zero function of $v$) and a part of mean zero on every fibre; the first factor contracts the former by $\lambda(G)$ and the second contracts the latter by $\lambda(H)$, and the two pieces stay orthogonal. Equality follows by testing on functions depending on one coordinate.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)
- [Rotation map of a regular multigraph](../zig-zag-product-and-explicit-expanders/rotation-map.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002.
- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
