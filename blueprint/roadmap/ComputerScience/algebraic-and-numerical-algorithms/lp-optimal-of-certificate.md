# LP optimality certificates

Consider the rational linear program: maximize $\sum_j c_j x_j$ subject to $\sum_j A_{ij} x_j = b_i$ for every $i$ and $x \ge 0$. Let $x$ be feasible, let $y \in \mathbb{Q}^m$ satisfy $c_j \le \sum_i y_i A_{ij}$ for every $j$, and suppose complementary slackness $x_j \big(\sum_i y_i A_{ij} - c_j\big) = 0$ holds for every $j$. Then every feasible $x'$ has $\sum_j c_j x'_j \le \sum_j c_j x_j$, so $x$ is optimal.
