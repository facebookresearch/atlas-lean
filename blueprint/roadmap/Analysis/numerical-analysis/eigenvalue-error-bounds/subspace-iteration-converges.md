# Convergence of subspace iteration

Let $A$ be an $n \times n$ complex matrix whose eigenvalues $\lambda_1, \dots, \lambda_n$, counted with algebraic multiplicity and ordered by decreasing modulus, satisfy $|\lambda_1| > |\lambda_2| > \dots > |\lambda_m| > |\lambda_{m+1}|$ for some $m < n$; so $\lambda_1, \dots, \lambda_m$ are algebraically simple. (For a repeated dominant eigenvalue the conclusion fails: for $A = \operatorname{diag}(2, 2, 1)$ and $x_1 = e_1 + e_2$ the normalized iterates stay at $(e_1 + e_2)/\sqrt2$.) Let $A = QTQ^*$ be a [Schur decomposition](../../../LinearAlgebra/matrix-decompositions/schur-decomposition/exists-unitary-group-is-upper-triangular.md), with $Q$ unitary and $T$ upper triangular, ordered so that the first $m$ diagonal entries of $T$ are $\lambda_1, \dots, \lambda_m$, and let $q_1, \dots, q_m$ be the first $m$ columns of $Q$, the Schur vectors associated with $\lambda_1, \dots, \lambda_m$; and for each $i \le m$ let $P_i$ be the [spectral projector](spectral-projectors.md) associated with $\lambda_1, \dots, \lambda_i$ (the sum of their spectral projectors). Let $X_0 = [x_1, \dots, x_m]$ satisfy

$$\operatorname{rank}\big(P_i\,[x_1, \dots, x_i]\big) = i \qquad (i = 1, \dots, m),$$

and let $X_k$ be obtained by orthonormalizing the columns of $A^k X_0$ by Gram–Schmidt. Then for each $i$ the $i$-th column of $X_k$ converges essentially to $q_i$: there are unimodular scalars $e^{i\theta_k}$ with $e^{i\theta_k} X_k e_i \to q_i$.

## Depends on

- [Spectral projectors of a square matrix](spectral-projectors.md)
- [Schur decomposition](../../../LinearAlgebra/matrix-decompositions/schur-decomposition/exists-unitary-group-is-upper-triangular.md)

## Related topics

- [Convergence of the power method](convergence-of-the-power-method.md): the case $m = 1$.

## Sources

- Y. Saad, *Numerical Methods for Large Eigenvalue Problems*, revised edition, SIAM, 2011, Section 5.1, Algorithms 5.1–5.2, the definition of essential convergence, and Theorem 5.1 with its proof through (5.2)–(5.3). <https://www-users.cse.umn.edu/~saad/eig_book_2ndEd.pdf>
