# Separated recurrences with torus weights

Let $A : \mathbb{Z}^2 \to \mathbb{C}$, $N_1 \in \mathbb{Z}$, $M \in \mathbb{N}$, and let $D_1, D_2$ be complex polynomials with $D_1(0) \ne 0$ and $D_2(0) \ne 0$. Suppose $A(n_1, n_2) = 0$ whenever $n_1 < N_1$ or $n_2 < N_1$, and that $A$ satisfies the separated recurrence

$$\sum_{i \le \deg D_1} \sum_{l \le \deg D_2} D_{1,i}\, D_{2,l}\, A(N_1 + m_1 - i,\ N_1 + m_2 - l) = 0 \quad \text{whenever } m_1 \ge M \text{ or } m_2 \ge M.$$

Let $P$ be the polynomial in four variables

$$P = \sum_{m < 2\max(M, \deg D_1)} \sum_{k < M} \sum_{i \le m} c_{m,k,i}\, X_0^m X_1^k X_2^i X_3^{m-i}, \qquad c_{m,k,i} = \sum_{p \le i} \sum_{t \le m-i} \sum_{l \le k} D_{1,p} D_{1,t} D_{2,l}\, A(N_1 + m - p - t,\ N_1 + k - l).$$

Then for all $b_1, b_2 \in \mathbb{C}$ (equal or zero allowed) there is $r > 0$ such that for $|X|, |Y| < r$ the series $S = \sum_{m_1, m_2 \ge 0} A(N_1 + m_1, N_1 + m_2)\, h_{m_1}(b_1, b_2)\, X^{m_1} Y^{m_2}$, with $h_{m}(b_1, b_2) = \sum_{i \le m} b_1^i b_2^{m-i}$, converges absolutely and

$$S \cdot D_1(b_1 X)\, D_1(b_2 X)\, D_2(Y) = P(X, Y, b_1, b_2).$$
