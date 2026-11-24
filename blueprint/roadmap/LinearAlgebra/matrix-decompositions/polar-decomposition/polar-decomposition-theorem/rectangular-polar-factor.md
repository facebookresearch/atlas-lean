# Canonical polar factor of a rectangular matrix

Let $G$ be a real $m \times n$ matrix. Choose a full singular value decomposition
$G = U \Sigma V^{\mathsf T}$, with $U$ and $V$ orthogonal and $\Sigma$ rectangular diagonal with
nonnegative entries. Form $D$ by replacing each positive diagonal entry of $\Sigma$ by $1$ and
keeping all other entries zero. The canonical polar factor is $P(G) = U D V^{\mathsf T}$.

If $r = \operatorname{rank} G$, the $r$ columns of $U$ and $V$ paired with positive singular values
form the compact factors $U_r$ and $V_r$. After ordering those columns first, the formula reads

$$P(G) = U_r V_r^{\mathsf T} = \sum_{i=1}^r u_i v_i^{\mathsf T}.$$

In particular, $P(0) = 0$.

## Sources

- N. Amsel, D. Persson, C. Musco and R. M. Gower, "The Polar Express: Optimal Matrix Sign Methods and Their Application to the Muon Algorithm", ICLR 2026, arXiv:2505.16932 (version 5), Section 1.1, equation (1), and the Notation paragraph at the end of Section 1 (polynomials of a matrix through its rank-reduced singular value decomposition).
- N. J. Higham, Functions of Matrices: Theory and Computation, SIAM (2008), Chapter 8 (the polar decomposition).
