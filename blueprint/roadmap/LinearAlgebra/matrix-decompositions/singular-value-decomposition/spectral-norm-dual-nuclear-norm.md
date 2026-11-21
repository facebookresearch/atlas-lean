# Duality of the spectral and nuclear norms

Let $G$ be a real $m \times n$ matrix with $m, n \ge 1$, let $k = \min(m, n)$, let
$r = \operatorname{rank} G$, and let $\sigma_1 \ge \dots \ge \sigma_k \ge 0$ be its singular values,
with compact singular value decomposition $G = U_r \Sigma_r V_r^{\mathsf{T}}$ and canonical polar
factor $P(G) = U_r V_r^{\mathsf{T}}$ ($P(0) = 0$). Write
$\langle A, B \rangle = \operatorname{tr}(A^{\mathsf{T}} B)$, $\|T\|_2$ for the spectral norm (the
largest singular value) and $\|G\|_* = \sigma_1 + \dots + \sigma_k$ for the nuclear norm. Then:

1. $\max_{\|T\|_2 \le 1} \langle G, T \rangle = \|G\|_*$: under the Frobenius pairing, the nuclear
   norm is the dual norm of the spectral norm.
2. The maximum is attained at $T = P(G)$, and also at $\sum_{i \le k} u_i v_i^{\mathsf{T}}$ for every
   thin singular value decomposition $G = \sum_{i \le k} \sigma_i u_i v_i^{\mathsf{T}}$.
3. Spectral-ball linear minimization: for every $\rho \ge 0$,
   $-\rho P(G) \in \operatorname{argmin}_{\|T\|_2 \le \rho} \langle G, T \rangle$, with minimum value
   $-\rho \|G\|_*$. For $\rho > 0$ the minimizer is unique if and only if $r = k$. For $\rho = 0$ the
   only feasible point is $0$, so the minimizer is trivially unique.

Remark (derived here, not stated in the cited papers): for $\rho > 0$ the set of minimizers is
$\{-\rho (P(G) + \tilde U Z \tilde V^{\mathsf{T}}) : \|Z\|_2 \le 1\}$, where the columns of
$\tilde U$ and $\tilde V$ are orthonormal bases of the orthogonal complement of the column space of
$G$ and of the kernel of $G$, and $Z$ ranges over real $(m - r) \times (n - r)$ matrices. Since
$\|P(G) + \tilde U Z \tilde V^{\mathsf{T}}\|_F^2 = r + \|Z\|_F^2$, the unique minimizer of least
Frobenius norm is $-\rho P(G)$. For $G = 0$ every point of the ball $\|T\|_2 \le \rho$ is a
minimizer.

Proof: $\langle G, T \rangle = \sum_{i \le r} \sigma_i u_i^{\mathsf{T}} T v_i$ and
$u_i^{\mathsf{T}} T v_i \le \|T\|_2$, which gives the bound; $u_i^{\mathsf{T}} P(G) v_i = 1$ for
$i \le r$ gives equality, and so does the thin product. For item 3 apply this to $-T / \rho$. A
minimizer $T$ with $\rho > 0$ must have $S = -T / \rho$ with $u_i^{\mathsf{T}} S v_i = 1$, hence
$S v_i = u_i$ and $S^{\mathsf{T}} u_i = v_i$, for every $i \le r$; so $S - P(G)$ maps the kernel of
$G$ into the orthogonal complement of its column space and vanishes on the row space, which is the
remark. When $r = k$ one of $m - r$ and $n - r$ is $0$, so $Z$ is empty and the minimizer is unique;
when $r < k$ every $Z$ with $\|Z\|_2 \le 1$ gives one. No von Neumann trace inequality is needed.

## Informally uses

- [Real singular value decomposition](real-singular-value-decomposition.md): mathematical
  prerequisite, the decomposition in which the pairing $\langle G, T \rangle$ is expanded and from
  which $P(G)$ is built.

## Sources

- J. Bernstein and L. Newhouse, "Old Optimizer, New Norm: An Anthology", arXiv:2409.20325 (version 2), Proposition 5, equations (18)–(19), its proof in Appendix B, equations (48)–(49), and Table 1.
- T. Pethick, W. Xie, K. Antonakopoulos, Z. Zhu, A. Silveti-Falls and V. Cevher, "Training Deep Learning Models with Norm-Constrained LMOs", ICML 2025, arXiv:2502.07529 (version 2), equation (2) (the linear minimization oracle) and Table 1 (the spectral-norm ball and its minimizer $-\rho U V^{\mathsf{T}}$).
