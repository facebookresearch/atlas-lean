# Zig-zag tower expanders on every vertex count by contraction

Let $H$ be a regular multigraph on $B$, $b = |B| > 1$, with label set $D$ and a bijection $B \to (D \times D)^2$, and let $c < 1$ satisfy $c^2 + \lambda(H) + \lambda(H)^2 \le c$, so that every level $G_t$ of the zig-zag tower ($G_1 = H^2$, $G_{t+1} = G_t^2 \circledcirc H$) has spectral expansion at most $c$. For every $n \ge 1$ there is a regular multigraph on exactly $n$ vertices whose degree and whose spectral expansion bound $\lambda < 1$ depend only on $H$ and $c$, not on $n$: take the first level with at least $n$ vertices (it has at most $b n$), contract it onto $n$ vertices by merging the vertices into groups of at most $b$, and pass to the lazy graph.

## Proof sketch

A contraction with inhabited fibres of size at most $|I|$ keeps every dart that crosses a cut, so the edge expansion drops by at most a factor depending on $|I|$; the lazy-graph Cheeger bound then gives $\lambda \le 1 - (1 - \lambda(G))^2/(16|I|^2)$. Applying this to the tower level with $|I| = b$ gives the explicit bound

$$\lambda \le 1 - \frac{(1 - c)^2}{16\, b^2},$$

for the lazy graph of degree $2bd$, where $d$ is the degree of the tower levels and the contracted graph is padded with loops to degree $bd$.

## Depends on

- [The zig-zag expander family](../zig-zag-product-and-explicit-expanders/zigzag-family.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [The zig-zag expander family consists of expanders](../zig-zag-product-and-explicit-expanders/is-ndlambda-graph-zigzag-family.md)
- [The lazy graph: spectral expansion from the second eigenvalue and from edge expansion](../expander-graph-operations/lazy-graph-spectral-bounds.md)

## Sources

- O. Reingold, S. Vadhan, A. Wigderson, "Entropy Waves, the Zig-Zag Graph Product, and New Constant-Degree Expanders", Annals of Mathematics, 2002, Theorems 3.2 and 3.3.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", web draft of January 2007, Section 16.4, the paragraph before Theorem 16.32 and Theorem 16.32.
- S. Hoory, N. Linial, A. Wigderson, "Expander Graphs and Their Applications", Bulletin of the American Mathematical Society, 2006.
