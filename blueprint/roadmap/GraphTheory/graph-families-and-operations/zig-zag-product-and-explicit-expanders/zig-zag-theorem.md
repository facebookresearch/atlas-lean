# Zig-zag theorem

Let $V$, $K$ and $L$ be finite sets, $G$ a [rotation map](rotation-map.md) on $V \times K$ describing an $(N_1, D_1, \lambda_1)$-graph and $H$ a rotation map on $K \times L$ describing a $(D_1, D_2, \lambda_2)$-graph. Then their [zig-zag product](zigzag.md) is an

$$\big(N_1 D_1,\ D_2^2,\ \lambda_1 + \lambda_2 + \lambda_2^2\big)\text{-graph}$$

(O. Reingold, S. Vadhan and A. Wigderson, Ann. of Math. 155 (2002), Theorem 3.2, the bound $f(\lambda_1, \lambda_2) \le \lambda_1 + \lambda_2 + \lambda_2^2$, proved in their Section 4.1; see also Theorem 1.3). This is the bound of the paper's basic analysis; the tighter bound of its Theorem 4.3 ("Thm. 3.2, improved", Section 4.2), which Reingold quotes as his Theorem 2.9, is stronger.

The proof follows Section 4.1 of the paper. The adjacency operator of the product factors as $\tilde B \tilde A \tilde B$, where $\tilde B$ applies $H$ inside every cloud $\{v\} \times K$ and $\tilde A$ is the permutation of $V \times K$ given by the rotation map of $G$. A vector $x$ orthogonal to the constants splits as $x = x^\parallel + x^\perp$, with $x^\parallel$ constant on clouds and $x^\perp$ summing to zero on each cloud. Then $\tilde B$ fixes $x^\parallel$ and shrinks $x^\perp$ by $\lambda_2$, and $\langle \tilde A x^\parallel, x^\parallel\rangle$ is the quadratic form of $G$ on the cloud averages, at most $\lambda_1 \lVert x^\parallel\rVert^2$. Expanding $\langle \tilde B \tilde A \tilde B x, x\rangle = \langle \tilde A \tilde B x, \tilde B x\rangle$ gives $\lvert\langle M x, x\rangle\rvert \le \lambda_1 p^2 + 2\lambda_2 p q + \lambda_2^2 q^2 \le (\lambda_1 + \lambda_2 + \lambda_2^2)\lVert x\rVert^2$ (normalised, with $p = \lVert x^\parallel\rVert$, $q = \lVert x^\perp\rVert$), and a [polarization argument](quadratic-form-bound-gives-norm-bound.md) turns the quadratic-form bound into the norm bound of the $(N, D, \lambda)$ definition.

With $G$ big and $H$ small, the product keeps $G$'s size up to the factor $D_1$, takes its degree $D_2^2$ from $H$ alone, and has small spectral parameter when both factors have. Iterating $G_{t+1} = G_t^2 \circledcirc H$ (labels renamed) from $G_0 = H^2$, for a single $(D^4, D, 1/5)$-graph $H$, gives an explicit family of $(D^{4(t+1)}, D^2, 2/5)$-graphs $G_t$ (Reingold, Vadhan and Wigderson, Theorem 1.4, who index the family from $G_1 = H^2$, so that their $G_t$ has $D^{4t}$ vertices; see [the zig-zag expander family consists of expanders](is-ndlambda-graph-zigzag-family.md)).

## Background

- [Squaring squares the spectral parameter](is-ndlambda-graph-square.md): the other operation of
  the iteration, which improves expansion at the cost of degree.
- [Undirected ST-connectivity is in L (Reingold)](../../../TheoryOfComputation/polynomial-time-problems/undirected-s-t-connectivity/ustcon-in-l.md):
  the best-known application.
