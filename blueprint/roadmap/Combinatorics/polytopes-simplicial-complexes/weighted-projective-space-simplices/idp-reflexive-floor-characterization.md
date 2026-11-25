# Floor criterion for IDP of reflexive weighted simplices

Let $q = (q_1, \dots, q_n)$ be
positive integers such that the weighted simplex
$\Delta_{(1,q)} = \operatorname{conv}(e_1, \dots, e_n, -\sum_i q_i e_i) \subseteq \mathbb{R}^n$ is
reflexive, and for each $j$ write $S_j = \sum_{i \ne j} q_i$. Then $\Delta_{(1,q)}$ has the
integer decomposition property if and only if the following holds for every $j$: for every
integer $b$ with $1 \le b < q_j$ and

$$b \lfloor (1 + S_j) / q_j \rfloor - \sum_{i \ne j} \lfloor b q_i / q_j \rfloor \ge 2$$

there is an integer $c$ with $1 \le c < b$ such that
$\lfloor b q_i / q_j \rfloor - \lfloor c q_i / q_j \rfloor = \lfloor (b - c) q_i / q_j \rfloor$
for every $i \ne j$ and

$$c \lfloor (1 + S_j) / q_j \rfloor - \sum_{i \ne j} \lfloor c q_i / q_j \rfloor = 1.$$

All differences are taken in the natural numbers, truncated at $0$.

## Sources

- Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60, Theorem 4.
