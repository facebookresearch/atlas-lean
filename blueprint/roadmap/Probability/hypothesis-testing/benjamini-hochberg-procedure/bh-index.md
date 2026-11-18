# Benjamini–Hochberg step-up index

Let $m \in \mathbb{N}$, $q \in \mathbb{R}$ and $p_0, \dots, p_{m-1} \in \mathbb{R}$. The Benjamini–Hochberg step-up index at level $q$ is the largest $k \in \{0, \dots, m\}$ such that at least $k$ p-values are at most $qk/m$:

$$k^* = \max\{k \in \{0, \dots, m\} : \#\{i : p_i \le qk/m\} \ge k\}.$$

The value $k = 0$ always qualifies.
