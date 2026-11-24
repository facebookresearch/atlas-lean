# The start of an alternating chain of $L$ pairs is reached within $L$ rounds

Let $\mu$ be
a partner array, let $L \ge 1$, and let $(i_1, j_1), \dots, (i_L, j_L)$ be pairs of a left and a
right vertex such that each $j_t$ is adjacent to $i_t$ with $\mu(j_t) \ne i_t$, each $j_{t+1}$ has
partner $\mu(j_{t+1}) = i_t$ for $t < L$, and $i_L$ is unmatched. Then $j_1$ is among the right
vertices reached within $L$ rounds of the alternating layered search for $\mu$.

From the unmatched end, each pair advances one round.
