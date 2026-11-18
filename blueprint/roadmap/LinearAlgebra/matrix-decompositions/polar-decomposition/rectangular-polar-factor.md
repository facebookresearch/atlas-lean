# Canonical polar factor of a rectangular matrix

Let $G$ be a real $m \times n$ matrix, let $k = \min(m, n)$ and let $r = \operatorname{rank} G$.
A real singular value decomposition $G = U \Sigma V^{\mathsf{T}}$, with $U$ and $V$ orthogonal,
columns $u_i$ and $v_i$, and singular values $\sigma_1 \ge \dots \ge \sigma_k \ge 0$ (after reordering the columns if
needed), is a *full* decomposition. Its first $k$ columns give a *thin* decomposition
$G = \sum_{i \le k} \sigma_i u_i v_i^{\mathsf{T}}$, and its first $r$ columns, those with
$\sigma_i > 0$, give the *compact* decomposition $G = U_r \Sigma_r V_r^{\mathsf{T}}$. The canonical
polar factor of $G$ is

$$P(G) = U_r V_r^{\mathsf{T}} = \sum_{i \le r} u_i v_i^{\mathsf{T}},$$

taken from the compact decomposition; $P(0) = 0$. Then:

1. $P(G)$ does not depend on the chosen decomposition, because
   $P(G) = G (G^{\mathsf{T}} G)^{+1/2} = (G G^{\mathsf{T}})^{+1/2} G$, where $(\cdot)^{+1/2}$ is the
   Moore–Penrose pseudo-inverse of the positive semidefinite square root.
2. $G = P(G) (G^{\mathsf{T}} G)^{1/2}$, and $P(G)$ is a partial isometry:
   $P(G)^{\mathsf{T}} P(G)$ is the orthogonal projection onto the row space of $G$ and
   $P(G) P(G)^{\mathsf{T}}$ the orthogonal projection onto its column space.
3. $P(G)$ is semi-orthogonal, that is $P(G) P(G)^{\mathsf{T}} = I_m$ or
   $P(G)^{\mathsf{T}} P(G) = I_n$, if and only if $r = k$.
4. If $G$ is square and invertible, $P(G) = U V^{\mathsf{T}}$ is the orthogonal factor $O$ of the
   unique decomposition $G = O S$ with $S$ symmetric positive definite, and
   $S = V \Sigma V^{\mathsf{T}} = (G^{\mathsf{T}} G)^{1/2}$.
5. $P(c G) = P(G)$ for every real $c > 0$.

The product "$U V^{\mathsf{T}}$" needs a stated decomposition. Read with a full decomposition it is
$U I_{m \times n} V^{\mathsf{T}}$, where $I_{m \times n}$ has ones on its diagonal, and this is the
thin product $\sum_{i \le k} u_i v_i^{\mathsf{T}}$. When $r = k$ the thin product equals $P(G)$ for
every choice of decomposition. When $r < k$ it does not: it is semi-orthogonal, $P(G)$ is not, and it
depends on the choice of the $u_i$ and $v_i$ with $\sigma_i = 0$.

Proof: from the compact decomposition, $(G^{\mathsf{T}} G)^{+1/2} = V_r \Sigma_r^{-1} V_r^{\mathsf{T}}$,
so $G (G^{\mathsf{T}} G)^{+1/2} = U_r V_r^{\mathsf{T}}$, and the left side involves only $G$;
likewise $(G G^{\mathsf{T}})^{+1/2} = U_r \Sigma_r^{-1} U_r^{\mathsf{T}}$ gives
$(G G^{\mathsf{T}})^{+1/2} G = U_r V_r^{\mathsf{T}}$. Item 2 follows from
$U_r V_r^{\mathsf{T}} \cdot V_r \Sigma_r V_r^{\mathsf{T}} = G$ and $V_r^{\mathsf{T}} V_r = I_r$.
For item 3, $P(G) P(G)^{\mathsf{T}} = U_r U_r^{\mathsf{T}}$ has rank $r$, so it is $I_m$ exactly when
$r = m$; likewise $P(G)^{\mathsf{T}} P(G) = I_n$ exactly when $r = n$; and $r \le k$. For item 5,
$U_r (c \Sigma_r) V_r^{\mathsf{T}}$ is a compact decomposition of $c G$. Item 4 is derived here, not
taken from the cited paper: when $r = m = n$, $G = (U V^{\mathsf{T}})(V \Sigma V^{\mathsf{T}})$ with
$U V^{\mathsf{T}}$ orthogonal and $V \Sigma V^{\mathsf{T}}$ symmetric positive definite, so uniqueness
of the polar decomposition of an invertible real matrix gives $O = U V^{\mathsf{T}}$.

Amsel, Persson, Musco and Gower define $\operatorname{polar}(M) = U V^{\mathsf{T}}$ and call it the
closest semi-orthogonal matrix to $M$; that description is exact only when $M$ has full rank
$r = k$. When $r < k$, $P(G)$ is not semi-orthogonal, and the nearest semi-orthogonal matrices,
treated in this section, are not unique.

## Informally uses

- [Real singular value decomposition](../singular-value-decomposition/real-singular-value-decomposition.md):
  mathematical prerequisite, the full decomposition from which the thin and compact decompositions,
  and with them $P(G)$, are read off.
- [Polar decomposition of invertible real matrices](polar-decomposition-gl-real.md): mathematical
  prerequisite for item 4 only, whose identification of $P(G)$ with the orthogonal factor uses the
  uniqueness of that decomposition.

## Sources

- N. Amsel, D. Persson, C. Musco and R. M. Gower, "The Polar Express: Optimal Matrix Sign Methods and Their Application to the Muon Algorithm", ICLR 2026, arXiv:2505.16932 (version 5), Section 1.1, equation (1), and the Notation paragraph at the end of Section 1 (polynomials of a matrix through its rank-reduced singular value decomposition).
- N. J. Higham, Functions of Matrices: Theory and Computation, SIAM (2008), Chapter 8 (the polar decomposition).
