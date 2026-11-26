# Sinkhorn's scaling theorem

Let $n \ge 1$ and let $A$ be a real $n \times n$ matrix with strictly positive entries. Then there are vectors $r, c \in \mathbb{R}^n$ with strictly positive entries such that the matrix with entries $r_i A_{ij} c_j$ is doubly stochastic: its entries are nonnegative and each row and each column sums to $1$.

## Idea

Sinkhorn's algorithm alternately rescales the rows and the columns of $A$ to sum to $1$; for a positive matrix it converges, and the limit is $\operatorname{diag}(r)\, A \operatorname{diag}(c)$. The scaling is unique up to multiplying $r$ by a constant and dividing $c$ by it. For nonnegative matrices with zero entries a scaling exists exactly when the matrix has total support, that is, it is nonzero and every positive entry lies on a positive diagonal (Sinkhorn and Knopp; the zero matrix satisfies the second condition vacuously but cannot be scaled); for symmetric matrices, the Csima–Datta theorem gives a symmetric scaling $\operatorname{diag}(d)\, A \operatorname{diag}(d)$ exactly when $A$ has total support. Matrix scaling appears in transportation and entropic optimal transport, in contingency tables, and in algorithms for the permanent.

## Statements

- [Sinkhorn's scaling theorem](sinkhorn-scaling.md)
- [Csima–Datta theorem](exists-symmetric-balancing-iff-has-total.md): the symmetric variant: the Csima–Datta theorem
- [Csima–Datta: sufficiency of total support](exists-symmetric-balancing-of-has-total.md): its sufficiency half
- [Scaling to prescribed row and column sums](scaling-to-prescribed-row-and-column-sums.md): a stronger form: rectangular nonnegative matrices and general positive margins (Menon; Brualdi; Sinkhorn–Knopp)
