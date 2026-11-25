# Von Neumann's trace inequality

Let $A$ and $B$ be real symmetric $d \times d$ matrices with eigenvalues $\alpha^\downarrow_0 \ge \dots \ge \alpha^\downarrow_{d-1}$ and $\beta^\downarrow_0 \ge \dots \ge \beta^\downarrow_{d-1}$ in decreasing order. Then

$$\operatorname{tr}(AB) \le \sum_{k=0}^{d-1} \alpha^\downarrow_k \beta^\downarrow_k.$$

## Idea

In orthonormal eigenbases $(u_i)$ of $A$ and $(v_j)$ of $B$, $\operatorname{tr}(AB) = \sum_{i,j} \alpha_i \beta_j \langle u_i, v_j \rangle^2$, and the matrix of the weights $\langle u_i, v_j \rangle^2$ is doubly stochastic. A linear function on doubly stochastic matrices is maximized at a permutation matrix (Birkhoff), so $\operatorname{tr}(AB)$ is at most $\sum_k \alpha_k \beta_{\tau(k)}$ for some pairing $\tau$, and the rearrangement inequality says that pairing the eigenvalues in the same order is best. The bound is attained when $A$ and $B$ share an eigenbasis ordered the same way. Pairing in opposite orders gives the lower bound. For symmetric matrices this refines von Neumann's inequality $|\operatorname{tr}(AB)| \le \sum_k \sigma_k(A)\sigma_k(B)$ for singular values.

## Statements

- [Von Neumann's trace inequality, sorted upper form](trace-mul-le-sum-eigenvalues-mul.md)
- [Von Neumann's trace inequality, sorted lower form](sum-eigenvalues-mul-rev-le-trace-mul.md): the lower bound, with eigenvalues paired in opposite orders
- [A pairing of eigenvalues bounds the trace of a product from above](exists-perm-trace-mul-le-sum-mul-eigenva.md): some pairing of eigenvalues bounds the trace from above
- [A pairing of eigenvalues bounds the trace of a product from below](exists-perm-sum-mul-eigenvalues-le-trace.md): some pairing bounds it from below
- [The trace of a product of symmetric matrices in their eigenbases](trace-mul-eq-sum-eigenvalues.md): the trace in the two eigenbases
- [The overlap matrix of two orthonormal bases is doubly stochastic](overlap-mem-doubly-stochastic.md): the overlap matrix is doubly stochastic
- [Linear functionals on doubly stochastic matrices are bounded below at a permutation](exists-perm-sum-le-of-mem-doubly-stochas.md): linear functions on doubly stochastic matrices are extremal at permutations
- [The quadratic form of a symmetric matrix in an orthonormal eigenbasis](inner-to-euclidean-lin-self-eq-sum.md): the quadratic form in an eigenbasis
