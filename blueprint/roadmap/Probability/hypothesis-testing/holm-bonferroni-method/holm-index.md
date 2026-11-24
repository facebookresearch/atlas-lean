# Holm's step-down count

Let $m \in \mathbb{N}$, $\alpha \in \mathbb{R}$ and $p_0, \dots, p_{m-1} \in \mathbb{R}$, and write $N(t) = \#\{i : p_i \le t\}$. Holm's step-down count at level $\alpha$ is the largest $r \in \{0, \dots, m\}$ such that

$$N\Big(\frac{\alpha}{m - k + 1}\Big) \ge k \quad \text{for every } k \in \{1, \dots, r\},$$

that is, for each $k \le r$ the $k$-th smallest p-value is at most $\alpha/(m - k + 1)$. The value $r = 0$ always qualifies.
