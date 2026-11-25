# Blum–Mansour decomposition

Over $T$ rounds with a finite nonempty set $K$ of actions, let $q_t(j, \cdot)$ be a probability distribution on actions for each copy $j$, and let the master distribution $p_t$ be a probability distribution that is stationary for these recommendations: $p_t(i) = \sum_j p_t(j)\, q_t(j, i)$ for all $t$ and $i$. Then for any losses $\ell_t(a)$, the swap regret of $p$ is at most $\sum_j R_j$, where $R_j$ is the external regret of copy $j$'s play $q_\cdot(j, \cdot)$ against the scaled losses $p_t(j)\, \ell_t(a)$.
