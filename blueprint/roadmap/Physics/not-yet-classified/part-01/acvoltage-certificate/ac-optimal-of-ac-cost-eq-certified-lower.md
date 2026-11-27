# Certified bound attained implies AC optimality

Consider a current-limited AC optimal power flow problem on $n$ buses and $m$ branches: for a voltage vector $V \in \mathbb{C}^n$, AC feasibility requires the active and reactive generation at each bus, the squared voltage magnitudes $|V_k|^2$ and the squared branch currents to lie within their limits, and the AC cost is $\sum_k c_k\,(P_k(V) + d_k)$, where $P_k(V)$ is the active injection at bus $k$, $d_k$ the active demand and $c_k$ the cost coefficient. Its semidefinite relaxation minimizes $\sum_k c_k\,(\operatorname{Re}\operatorname{tr}(A^P_k W) + d_k)$ over Hermitian positive semidefinite $W$ subject to the same limits written as $\operatorname{Re}\operatorname{tr}(A_i W) \le b_i$, with no rank constraint; the lift of $V$ is $VV^{\mathsf H}$. A dual witness consists of one real multiplier $\lambda_i$ per inequality and a matrix $F \in \mathbb{C}^{n \times k}$; its certified bound is $\ell = \sum_k c_k d_k - \sum_i \lambda_i b_i$.

Assume every multiplier is nonnegative, $\lambda_i \ge 0$, and the dual slack factors exactly: $C + \sum_i \lambda_i A_i = F F^{\mathsf H}$, where $C = \sum_k c_k A^P_k$. If $V^\star$ is AC feasible and its AC cost equals $\ell$, then

1. the AC cost of $V^\star$ is at most the AC cost of every AC-feasible $V$; and
2. the relaxation cost of the lift $V^\star V^{\star\mathsf H}$ is at most the relaxation cost of every relaxation-feasible $W$.
