# Nearest semi-orthogonal matrices

Let $G$ be a real $m \times n$ matrix, $k = \min(m, n)$, $r = \operatorname{rank} G$ and
$\sigma_1 \ge \dots \ge \sigma_k \ge 0$ its singular values, and call an $m \times n$ matrix $A$
semi-orthogonal if $A A^{\mathsf{T}} = I_m$ or $A^{\mathsf{T}} A = I_n$. For every semi-orthogonal $A$,
$\|A - G\|_F^2 = k - 2 \langle A, G \rangle + \|G\|_F^2$ with $\langle A, B \rangle = \operatorname{tr}(A^{\mathsf T} B)$,
and $\langle A, G \rangle \le \sigma_1 + \dots + \sigma_k$. Hence, for every thin singular value
decomposition $G = \sum_{i \le k} \sigma_i u_i v_i^{\mathsf{T}}$, the matrix $\sum_{i \le k} u_i v_i^{\mathsf{T}}$
is a semi-orthogonal matrix nearest to $G$ in the Frobenius norm. The nearest semi-orthogonal matrix is
unique if and only if $r = k$, and then it is the canonical polar factor $P(G) = U_r V_r^{\mathsf{T}}$
of a compact singular value decomposition $G = U_r \Sigma_r V_r^{\mathsf{T}}$.

## Idea

All semi-orthogonal matrices have the same Frobenius norm, $\sqrt{k}$, so the nearest one to $G$ is
the one with the largest inner product with $G$. By the duality of the spectral and nuclear norms that
inner product is at most $\sigma_1 + \dots + \sigma_k$, and the product $\sum_i u_i v_i^{\mathsf T}$ of
a thin singular value decomposition attains it. When $G$ has full rank $k$ the answer is the polar
factor; otherwise the singular vectors of the zero singular values can be chosen in several ways, and
the nearest matrix is not unique.

## Statements

- [Nearest semi-orthogonal matrices](nearest-semi-orthogonal-matrix.md)

## Background

- [Polar decomposition](../polar-decomposition-theorem/README.md): the canonical polar factor
- [Duality of the spectral and nuclear norms](../../singular-value-decomposition/duality-of-the-spectral-and-nuclear-norms/README.md): the bound on the inner product, used in the proof
