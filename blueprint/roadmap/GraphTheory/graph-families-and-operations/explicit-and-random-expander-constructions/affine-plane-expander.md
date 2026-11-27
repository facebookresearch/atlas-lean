# The affine-plane expander over a finite field

Let $K$ be a finite field. The affine-plane graph is the $|K|$-regular multigraph on $K \times K$ in which the edge labelled $c \in K$ at $(a, b)$ leads to $(c, ac - b)$ and arrives with label $a$; this rotation map is an involution. For every $f : K \times K \to \mathbb{R}$, two steps of its walk give

$$(W^2 f)(a, b) = \mathbb{E}_p f(p) + \frac{1}{|K|}\Bigl(f(a, b) - \mathbb{E}_{y \in K} f(a, y)\Bigr),$$

and consequently its spectral expansion is at most $\sqrt{1/|K|}$.

## Proof sketch

Two steps from $(a, b)$ through $(c, ac - b)$ reach $(c', c'c - ac + b)$; summing over $c, c'$ shows that every point outside the row $\{a\} \times K$ is reached exactly once, which gives the averaging identity. On mean-zero $f$ the identity says $\langle f, W^2 f \rangle \le \frac{1}{|K|}\mathbb{E} f^2$, and self-adjointness turns this into $\lambda^2 \le 1/|K|$.

## Depends on

- [Rotation map of a regular multigraph](../zig-zag-product-and-explicit-expanders/rotation-map.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002.
