# Explicit arithmetic constant-degree expanders on every number of vertices

Let $K$ be a finite field with $q \ge 256$ elements and an explicit numbering. Tensoring two affine-plane graphs over $K$ and zig-zagging twice with the affine-plane graph gives a $q^2$-regular multigraph on $q^8$ vertices with spectral expansion at most $3r + 2r^2 \le 1/5$, where $r = q^{-1/2}$; it is a valid base for the zig-zag tower, every level of which then has spectral expansion at most $2/5$. Contracting a tower level to an arbitrary size through bounded fibres and passing to the lazy graph yields, for every $n \ge 1$, a rotation map on exactly $n$ vertices of degree $2q^{12}$ with spectral expansion at most $1 - 9/(400 q^{16})$. For $K = \mathbb{Z}/257$ this is an explicit family whose degree and spectral gap do not depend on $n$, computed by field arithmetic without search.

## Proof sketch

The affine-plane bound $\lambda \le r$, the tensor bound $\max$, and two applications of the zig-zag theorem $\lambda_1 + \lambda_2 + \lambda_2^2$ give $3r + 2r^2$, at most $1/5$ for $q \ge 256$. The zig-zag tower keeps $\lambda \le 2/5$. Choosing the first tower level with at least $n$ vertices, contracting each fibre of bounded size to a vertex preserves edge expansion up to the fibre size, and Cheeger's inequality for the lazy graph converts this into the stated uniform gap.

## Depends on

- [The affine-plane expander over a finite field](affine-plane-expander.md)
- [Spectral expansion of the tensor product of rotation maps](../expander-graph-operations/tensor-product-of-rotation-maps.md)
- [The zig-zag expander family](../zig-zag-product-and-explicit-expanders/zigzag-family.md)

## Proof depends on

- [The affine-plane expander over a finite field](affine-plane-expander.md)
- [Spectral expansion of the tensor product of rotation maps](../expander-graph-operations/tensor-product-of-rotation-maps.md)
- [Zig-zag theorem](../zig-zag-product-and-explicit-expanders/zig-zag-theorem.md)
- [The zig-zag expander family consists of expanders](../zig-zag-product-and-explicit-expanders/is-ndlambda-graph-zigzag-family.md)
- [The lazy graph: spectral expansion from the second eigenvalue and from edge expansion](../expander-graph-operations/lazy-graph-spectral-bounds.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002.
- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
