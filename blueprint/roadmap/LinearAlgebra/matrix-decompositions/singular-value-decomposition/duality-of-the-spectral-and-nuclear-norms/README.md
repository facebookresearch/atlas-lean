# Duality of the spectral and nuclear norms

Let $G$ be a real $m \times n$ matrix with $m, n \ge 1$, let $k = \min(m, n)$ and $r = \operatorname{rank} G$,
let $\sigma_1 \ge \dots \ge \sigma_k \ge 0$ be its singular values, and let
$P(G) = U_r V_r^{\mathsf{T}}$ be its canonical polar factor, from a compact singular value
decomposition $G = U_r \Sigma_r V_r^{\mathsf{T}}$ ($P(0) = 0$). For the pairing
$\langle A, B \rangle = \operatorname{tr}(A^{\mathsf{T}} B)$, the nuclear norm
$\|G\|_* = \sigma_1 + \dots + \sigma_k$ is the dual norm of the spectral norm:
$\max_{\|T\|_2 \le 1} \langle G, T \rangle = \|G\|_*$, attained at $T = P(G)$ and at
$\sum_{i \le k} u_i v_i^{\mathsf{T}}$ for every thin singular value decomposition
$G = \sum_{i \le k} \sigma_i u_i v_i^{\mathsf{T}}$. Consequently, for every $\rho \ge 0$, $-\rho P(G)$
minimizes $\langle G, T \rangle$ over $\|T\|_2 \le \rho$, with minimum $-\rho \|G\|_*$, and for
$\rho > 0$ this minimizer is unique if and only if $r = k$.

## Idea

On vectors the $\ell^\infty$ and $\ell^1$ norms are dual; on matrices the spectral norm, the largest
singular value, and the nuclear norm, their sum, play these roles. In singular coordinates
$\langle G, T \rangle = \sum_{i \le r} \sigma_i \, u_i^{\mathsf T} T v_i$, and each
$u_i^{\mathsf T} T v_i$ is at most $\|T\|_2$, with equality for the polar factor. The minimization
form describes the steepest descent direction in a spectral-norm ball, the step of optimizers that
orthogonalize their updates: it is the negative polar factor of the gradient.

## Statements

- [Duality of the spectral and nuclear norms](spectral-norm-dual-nuclear-norm.md)

## Background

- [Polar decomposition](../../polar-decomposition/polar-decomposition-theorem/README.md): the canonical polar factor
