# Canonical polar factor of a rectangular matrix

Let $G$ be a real $m \times n$ matrix. Choose a full singular value decomposition
$G = U \Sigma V^{\mathsf T}$, with $U$ and $V$ orthogonal and $\Sigma$ rectangular diagonal with
nonnegative entries. Form $D$ by replacing each positive diagonal entry of $\Sigma$ by $1$ and
keeping all other entries zero. The canonical polar factor is $P(G) = U D V^{\mathsf T}$.

If $r = \operatorname{rank} G$, the $r$ columns of $U$ and $V$ paired with positive singular values
form the compact factors $U_r$ and $V_r$. After ordering those columns first, the formula reads

$$P(G) = U_r V_r^{\mathsf T} = \sum_{i=1}^r u_i v_i^{\mathsf T}.$$

In particular, $P(0) = 0$.

The definition follows the rank-reduced (compact SVD) convention. For every $G$, $P(G)$ is the
partial isometry $P$ of the canonical polar decomposition $G = P H$: the unique decomposition with
$P$ a partial isometry, $H$ symmetric positive semidefinite and the row space of $P$ equal to the
range of $H$, in which $H = (G^{\mathsf T} G)^{1/2}$. If $G$ has full rank $\min(m, n)$, $P(G)$ is
semi-orthogonal ($P P^{\mathsf T} = I_m$ or $P^{\mathsf T} P = I_n$) and is the unique polar factor
of $G$ with orthonormal columns (or, when $m < n$, the transpose of that of $G^{\mathsf T}$). It is
also a semi-orthogonal matrix nearest to $G$ in every unitarily invariant norm, and the unique
nearest one in the Frobenius norm. In the spectral norm a nearest semi-orthogonal matrix need not
be unique: for $G = \operatorname{diag}(3, 1)$, both $I$ and $\operatorname{diag}(1, -1)$ attain the
least distance, $2$. If the rank of $G$ is less than $\min(m, n)$, $P(G)$ is not semi-orthogonal.

## Sources

- N. Amsel, D. Persson, C. Musco and R. M. Gower, "The Polar Express: Optimal Matrix Sign Methods and Their Application to the Muon Algorithm", ICLR 2026, arXiv:2505.16932 (version 5), Section 1.1, equation (1), and the Notation paragraph at the end of Section 1 (polynomials of a matrix through its rank-reduced singular value decomposition); they describe the factor as the closest semi-orthogonal matrix without naming a norm, and this definition gives a nearest semi-orthogonal matrix only at full rank.
- N. J. Higham, Functions of Matrices: Theory and Computation, SIAM (2008), Chapter 8, Theorem 8.1 (the polar decomposition with orthonormal columns, unique at full rank), Theorem 8.3 (the canonical polar decomposition) and Theorem 8.4 (the polar factor as a nearest matrix with orthonormal columns in every unitarily invariant norm, and the unique nearest one in the Frobenius norm at full rank).
