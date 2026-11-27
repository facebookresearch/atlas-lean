# The balanced replacement product of two expanders is an expander

Let $G$ (rotation map on $V \times K$) and $H$ (rotation map on $K \times L$) be regular multigraphs and $G \circledR H$ their balanced replacement product, a $2|L|$-regular multigraph on $V \times K$. With $\lambda$ the spectral expansion and $G \circledcirc H$ the zig-zag product,

$$\lambda(G \circledR H)^3 \le \frac78 + \frac{\lambda(G \circledcirc H)}{8}, \qquad \lambda(G \circledR H) \le 1 - \frac{(1 - \lambda(G))(1 - \lambda(H))^2}{24}.$$

In particular $\lambda(G \circledR H) < 1$ whenever $\lambda(G) < 1$ and $\lambda(H) < 1$.

## Proof sketch

Expand the cube $\frac18(\tilde B + \tilde A)^3$ into eight words; one of them is the zig-zag walk operator $\tilde B \tilde A \tilde B$ and the other seven are contractions of norm at most one on mean-zero functions. This gives the first bound, and the zig-zag theorem in gap form, $1 - \lambda(G \circledcirc H) \ge (1 - \lambda(G))(1 - \lambda(H))^2$, together with $(1 - x/8)^{1/3} \le 1 - x/24$ gives the second.

## Depends on

- [Balanced replacement product of rotation maps](balanced-replacement-product.md)
- [Zig-zag product of rotation maps](../zig-zag-product-and-explicit-expanders/zigzag.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Zig-zag theorem, spectral-gap form](../zig-zag-product-and-explicit-expanders/zig-zag-theorem-gap-form.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
