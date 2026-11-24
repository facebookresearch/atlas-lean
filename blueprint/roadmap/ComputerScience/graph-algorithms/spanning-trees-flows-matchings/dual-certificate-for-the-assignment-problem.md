# Dual certificate for the assignment problem

Let $w$ be a real $n \times n$ cost matrix, let $u, v \in \mathbb{R}^n$ satisfy $u_i + v_j \le w_{ij}$ for all $i, j$, and let $\sigma$ be a permutation with $u_i + v_{\sigma(i)} = w_{i\sigma(i)}$ for every $i$. Then $\sum_i w_{i\sigma(i)} \le \sum_i w_{i\tau(i)}$ for every permutation $\tau$, so $\sigma$ is a minimum-cost assignment.

Proof. For every $\tau$, $\sum_i w_{i\tau(i)} \ge \sum_i (u_i + v_{\tau(i)}) = \sum_i u_i + \sum_j v_j = \sum_i (u_i + v_{\sigma(i)}) = \sum_i w_{i\sigma(i)}$, since $\tau$ and $\sigma$ are bijections.
