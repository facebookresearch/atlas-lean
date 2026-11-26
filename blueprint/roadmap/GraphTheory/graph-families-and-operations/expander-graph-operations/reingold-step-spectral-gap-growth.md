# Reingold's transformation step multiplies the spectral gap

Let $H$ be a regular multigraph on a vertex set $B$ with label set $E$ together with a bijection $e : B \to (E \times E)^2$ (so $|B| = |E|^4$), and let $G$ be a $|B|$-regular multigraph on $V$ whose labels are identified with $B$. One step of Reingold's transformation is $G' = ((G \circledcirc H)^2)$ with labels renamed into $B$ through $e$, a $|B|$-regular multigraph on $V \times B$. With $\lambda$ the spectral expansion,

$$\lambda(G') \le \bigl(1 - (1 - \lambda(G))(1 - \lambda(H))^2\bigr)^2,$$

and if $\lambda(H) \le 1/5$ and $0 \le \gamma \le 1 - \lambda(G)$, then $1 - \lambda(G') \ge \min\{6\gamma/5,\ 1/5\}$. Iterating $O(\log |V|)$ times therefore turns every connected component with an inverse-polynomial gap into a constant-degree expander, without merging components.

## Proof sketch

The zig-zag theorem in gap form gives $1 - \lambda(G \circledcirc H) \ge (1 - \lambda(G))(1 - \lambda(H))^2$, relabelling does not change the spectral expansion, and squaring squares it. With $\lambda(H) \le 1/5$ the gap $\gamma$ becomes at least $1 - (1 - 16\gamma/25)^2$, which is at least $\min\{6\gamma/5, 1/5\}$ by a one-variable estimate.

## Depends on

- [Zig-zag product of rotation maps](../zig-zag-product-and-explicit-expanders/zigzag.md)
- [Square of a rotation map](../zig-zag-product-and-explicit-expanders/square.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Zig-zag theorem, spectral-gap form](../zig-zag-product-and-explicit-expanders/zig-zag-theorem-gap-form.md)
- [Squaring squares the spectral parameter](../zig-zag-product-and-explicit-expanders/is-ndlambda-graph-square.md)
- [Powers of a regular multigraph: the spectral expansion is multiplicative](spectral-expansion-of-graph-powers.md)

## Sources

- O. Reingold, "Undirected Connectivity in Log-Space", Journal of the ACM, 2008.
- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
