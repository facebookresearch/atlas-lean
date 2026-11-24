# Canonical polar factor of a rectangular matrix

Let $G$ be a real $m \times n$ matrix, let $k = \min(m, n)$ and let $r = \operatorname{rank} G$.
A real singular value decomposition $G = U \Sigma V^{\mathsf{T}}$, with $U$ and $V$ orthogonal,
columns $u_i$ and $v_i$, and singular values $\sigma_1 \ge \dots \ge \sigma_k \ge 0$ (after reordering the columns if
needed), is a *full* decomposition. Its first $k$ columns give a *thin* decomposition
$G = \sum_{i \le k} \sigma_i u_i v_i^{\mathsf{T}}$, and its first $r$ columns, those with
$\sigma_i > 0$, give the *compact* decomposition $G = U_r \Sigma_r V_r^{\mathsf{T}}$. The canonical
polar factor of $G$ is

$$P(G) = U_r V_r^{\mathsf{T}} = \sum_{i \le r} u_i v_i^{\mathsf{T}},$$

taken from the compact decomposition; $P(0) = 0$.

## Depends on

- [Real singular value decomposition](../../singular-value-decomposition/singular-value-decomposition-theorem/real-singular-value-decomposition.md)

## Sources

- N. Amsel, D. Persson, C. Musco and R. M. Gower, "The Polar Express: Optimal Matrix Sign Methods and Their Application to the Muon Algorithm", ICLR 2026, arXiv:2505.16932 (version 5), Section 1.1, equation (1), and the Notation paragraph at the end of Section 1 (polynomials of a matrix through its rank-reduced singular value decomposition).
- N. J. Higham, Functions of Matrices: Theory and Computation, SIAM (2008), Chapter 8 (the polar decomposition).
