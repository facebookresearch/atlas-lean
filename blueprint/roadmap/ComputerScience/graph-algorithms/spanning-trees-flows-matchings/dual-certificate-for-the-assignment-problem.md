# Dual certificate for the assignment problem

Let $w$ be a real $n \times n$ cost matrix, let $u, v \in \mathbb{R}^n$ satisfy $u_i + v_j \le w_{ij}$ for all $i, j$, and let $\sigma$ be a permutation with $u_i + v_{\sigma(i)} = w_{i\sigma(i)}$ for every $i$. Then $\sum_i w_{i\sigma(i)} \le \sum_i w_{i\tau(i)}$ for every permutation $\tau$, so $\sigma$ is a minimum-cost assignment.

Proof. For every $\tau$, $\sum_i w_{i\tau(i)} \ge \sum_i (u_i + v_{\tau(i)}) = \sum_i u_i + \sum_j v_j = \sum_i (u_i + v_{\sigma(i)}) = \sum_i w_{i\sigma(i)}$, since $\tau$ and $\sigma$ are bijections.

## Sources

- T. Ralphs, *Introduction to Mathematical Programming*, IE406 Lecture 19 (The assignment problem), Lehigh University, slides "The Dual of the Assignment Problem", "The Complementary Slackness Conditions", <https://coral.ise.lehigh.edu/~ted/files/ie406/lectures/Lecture19.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
