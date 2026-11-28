# Nelson–Aalen jumps out of a state with an empty delayed-entry risk set vanish

Let $\iota$ be a finite set of states and $k$, $n$ natural numbers. Delayed-entry multi-state data on $k$ grid times and $n$ subjects consist of

- strictly increasing grid times $t_0 < t_1 < \dots < t_{k-1}$;
- for each subject $i$, an entry index $\epsilon_i$, either a grid index or $\bot$ (below every grid index);
- for each subject $i$, an exit grid index $x_i$;
- for each subject $i$, a state path $s_i(0), s_i(1), \dots, s_i(k) \in \iota$, where $s_i(j)$ is read as the state just before $t_j$ and $s_i(j+1)$ as the state at $t_j$;

such that $\epsilon_i < x_i$ for every subject $i$. For a grid index $j$ and states $h, l$, the delayed-entry at-risk and transition counts are

$$Y_h(t_j) = \#\{i : \epsilon_i < j \le x_i,\ s_i(j) = h\}, \qquad N_{hl}(t_j) = \#\{i : \epsilon_i < j \le x_i,\ s_i(j) = h,\ s_i(j+1) = l\}.$$

The delayed-entry Nelson–Aalen jump at $t_j$ is the matrix $\Delta_j \in \mathbb{R}^{\iota \times \iota}$ with

$$\Delta_j(h, l) = \frac{N_{hl}(t_j)}{Y_h(t_j)} \ (h \ne l), \qquad \Delta_j(h, h) = -\frac{\sum_{l' \ne h} N_{hl'}(t_j)}{Y_h(t_j)},$$

with real division, $x/0 = 0$.

For every grid index $j$ and state $h$ with $Y_h(t_j) = 0$, and every state $l$,

$$\Delta_j(h, l) = 0.$$
