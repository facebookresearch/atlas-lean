# Delayed-entry multi-state counts as grouped multi-state data

Let $\iota$ be a set of states and $k$, $n$ natural numbers. Delayed-entry multi-state data on $k$ grid times and $n$ subjects consist of

- strictly increasing grid times $t_0 < t_1 < \dots < t_{k-1}$;
- for each subject $i$, an entry index $\epsilon_i$, either a grid index or $\bot$ (below every grid index);
- for each subject $i$, an exit grid index $x_i$;
- for each subject $i$, a state path $s_i(0), s_i(1), \dots, s_i(k) \in \iota$, where $s_i(j)$ is read as the state just before $t_j$ and $s_i(j+1)$ as the state at $t_j$;

such that $\epsilon_i < x_i$ for every subject $i$. For a grid index $j$ and states $h, l$, the delayed-entry at-risk and transition counts are

$$Y_h(t_j) = \#\{i : \epsilon_i < j \le x_i,\ s_i(j) = h\}, \qquad N_{hl}(t_j) = \#\{i : \epsilon_i < j \le x_i,\ s_i(j) = h,\ s_i(j+1) = l\}.$$

Grouped multi-state data on $\iota$ at $k$ times consist of strictly increasing observation times, a transition count for each time and each ordered pair of states, and an at-risk count for each time and state.

The grouped multi-state data of delayed-entry multi-state data have observation times $t_0 < \dots < t_{k-1}$, transition counts $N_{hl}(t_j)$ and at-risk counts $Y_h(t_j)$. For $l = h$, $N_{hh}(t_j)$ counts the subjects under observation at $t_j$ that are in $h$ both just before and at $t_j$.
