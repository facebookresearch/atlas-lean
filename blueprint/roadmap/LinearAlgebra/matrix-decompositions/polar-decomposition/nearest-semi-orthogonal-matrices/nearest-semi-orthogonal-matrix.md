# Nearest semi-orthogonal matrices

Let $G$ be a real $m \times n$ matrix, let $k = \min(m, n)$, let $r = \operatorname{rank} G$, and
let $\sigma_1 \ge \dots \ge \sigma_k \ge 0$ be its singular values. Write
$\langle A, B \rangle = \operatorname{tr}(A^{\mathsf{T}} B)$ and call an $m \times n$ matrix $A$
semi-orthogonal if $A A^{\mathsf{T}} = I_m$ or $A^{\mathsf{T}} A = I_n$. Let
$P(G) = U_r V_r^{\mathsf{T}}$ be the canonical polar factor, built from a compact singular value
decomposition $G = U_r \Sigma_r V_r^{\mathsf{T}}$ ($P(0) = 0$). Then:

1. For every semi-orthogonal $A$,
   $\|A - G\|_F^2 = k - 2 \langle A, G \rangle + \|G\|_F^2$ and
   $\langle A, G \rangle \le \sigma_1 + \dots + \sigma_k$.
2. Hence, for every thin singular value decomposition $G = \sum_{i \le k} \sigma_i u_i v_i^{\mathsf{T}}$,
   the matrix $\sum_{i \le k} u_i v_i^{\mathsf{T}}$ is a semi-orthogonal matrix nearest to $G$ in
   Frobenius norm.
3. The nearest semi-orthogonal matrix is unique if and only if $r = k$, and then it equals $P(G)$.
4. If $r < k$, it is not unique: changing the signs of the $v_i$ with $\sigma_i = 0$ in a thin
   decomposition gives a second one.

Remark (derived here, not stated in the cited paper): the nearest semi-orthogonal matrices are
exactly the matrices $P(G) + \tilde U Q \tilde V^{\mathsf{T}}$, where the columns of $\tilde U$ and
$\tilde V$ are orthonormal bases of the orthogonal complement of the column space of $G$ and of the
kernel of $G$, and $Q$ is any semi-orthogonal $(m - r) \times (n - r)$ matrix. When $r = k$, one of
$m - r$ and $n - r$ is $0$, $Q$ is empty and the set is $\{P(G)\}$.

Proof: a semi-orthogonal $A$ has $\|A\|_F^2 = \operatorname{tr}(A^{\mathsf{T}} A) = k$, which gives
the identity; it also has spectral norm at most $1$ (exactly $1$ unless $\min(m, n) = 0$), so the duality of the spectral and nuclear norms gives
$\langle A, G \rangle = \sum_{i \le r} \sigma_i u_i^{\mathsf{T}} A v_i \le \sum_i \sigma_i$. The thin
product of item 2 is semi-orthogonal and attains the bound. Equality forces
$u_i^{\mathsf{T}} A v_i = 1$, so $A v_i = u_i$ and $A^{\mathsf{T}} u_i = v_i$, for every $i \le r$.
If $r = n \le m$, this fixes $A$ on all of $\mathbb{R}^n$, and if $r = m \le n$, it fixes
$A^{\mathsf{T}}$ on all of $\mathbb{R}^m$; either way $A = P(G)$. If $r < k$, the sign change of
item 4 gives a different semi-orthogonal matrix with the same inner product.

## Depends on

- [Canonical polar factor of a rectangular matrix](../polar-decomposition-theorem/rectangular-polar-factor.md)

## Informally uses

- [Real singular value decomposition](../../singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md):
  mathematical prerequisite, the decomposition whose thin and compact forms give the minimizers.
- [Duality of the spectral and nuclear norms](../../singular-value-decomposition/duality-of-the-spectral-and-nuclear-norms/spectral-norm-dual-nuclear-norm.md):
  mathematical prerequisite, the bound $\langle A, G \rangle \le \sigma_1 + \dots + \sigma_k$ for
  matrices $A$ of spectral norm at most $1$, used in the proof.

## Sources

- J. Bernstein and L. Newhouse, "Old Optimizer, New Norm: An Anthology", arXiv:2409.20325 (version 2), Proposition 4, equation (17) (uniqueness if and only if full rank), and its proof in Appendix B, equations (44)–(47) (the bound and the sign change).
- N. J. Higham, Functions of Matrices: Theory and Computation, SIAM (2008), Chapter 8 (the best-approximation property of the polar factor).
