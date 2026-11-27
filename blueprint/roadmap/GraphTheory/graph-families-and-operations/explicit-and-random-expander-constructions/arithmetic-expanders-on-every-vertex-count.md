# Explicit arithmetic constant-degree expanders on every number of vertices

Let $K$ be a finite field with $q \ge 256$ elements and an explicit numbering. Tensoring two affine-plane graphs over $K$ and zig-zagging twice with the affine-plane graph gives a $q^2$-regular multigraph on $q^8$ vertices with spectral expansion at most $3r + 2r^2 \le 1/5$, where $r = q^{-1/2}$; it is a valid base for the zig-zag tower, every level of which then has spectral expansion at most $2/5$. Merging the vertices of a tower level into groups of bounded size, so as to leave exactly $n$ vertices, and passing to the lazy graph yields, for every $n \ge 1$, an explicit regular multigraph on exactly $n$ vertices of degree $D_q$ with spectral expansion at most $\lambda_q < 1$, where $D_q$ and $\lambda_q$ depend only on $q$ and not on $n$.

## Proof sketch

The affine-plane bound $\lambda \le r$, the tensor bound $\max$, and two applications of the zig-zag theorem $\lambda_1 + \lambda_2 + \lambda_2^2$ give $3r + 2r^2$, at most $1/5$ for $q \ge 256$. The zig-zag tower keeps $\lambda \le 2/5$. Choosing the first tower level with at least $n$ vertices, contracting each fibre of bounded size to a vertex preserves edge expansion up to the fibre size, and Cheeger's inequality for the lazy graph converts this into a uniform gap.

Explicit constants: the tower levels have degree $q^4$ and $q^{8t}$ vertices, so the first level with at least $n$ vertices has at most $q^8 n$, and it contracts onto $n$ vertices through inhabited fibres of at most $q^8$ vertices, giving degree at most $q^{12}$ after padding with loops. A level has edge expansion at least $(1 - 2/5)\,q^4/2 = 3q^4/10$, and a contraction with inhabited fibres keeps every dart that crosses a cut, so the contracted graph keeps this edge expansion. The lazy graph has degree $2q^{12}$, and the lazy Cheeger bound $1 - h^2/(4D^2)$ with $D = q^{12}$ and $h = 3q^4/10$ gives spectral expansion at most $1 - 9/(400 q^{16})$, so $D_q = 2q^{12}$ and $\lambda_q = 1 - 9/(400 q^{16})$ work. For $K = \mathbb{Z}/257$ every step is computed by field arithmetic without search.

## Depends on

- [The affine-plane expander over a finite field](affine-plane-expander.md)
- [Spectral expansion of the tensor product of rotation maps](../expander-graph-operations/tensor-product-of-rotation-maps.md)
- [The zig-zag expander family](../zig-zag-product-and-explicit-expanders/zigzag-family.md)

## Proof depends on

- [Zig-zag theorem](../zig-zag-product-and-explicit-expanders/zig-zag-theorem.md)
- [The zig-zag expander family consists of expanders](../zig-zag-product-and-explicit-expanders/is-ndlambda-graph-zigzag-family.md)
- [The lazy graph: spectral expansion from the second eigenvalue and from edge expansion](../expander-graph-operations/lazy-graph-spectral-bounds.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002, Proposition 2.4, Theorems 3.2 and 3.3, Lemma 5.1 and Proposition 5.2.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", web draft of January 2007, Section 16.4, the paragraph before Theorem 16.32 and Theorem 16.32.
- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
