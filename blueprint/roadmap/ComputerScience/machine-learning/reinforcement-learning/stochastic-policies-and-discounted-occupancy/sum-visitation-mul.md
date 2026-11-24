# Occupancy averages

Let $P$ be a row-stochastic matrix on a finite set $S$ (nonnegative entries, each row summing to $1$) and let $0 \le \gamma < 1$. For every function $f : S \to \mathbb{R}$ and state $s_0$,

$$\sum_s d_{s_0}(s)\, f(s) = (1 - \gamma)\, V_f(s_0) = (1-\gamma)\,\mathbb{E}\Bigl[\sum_{t\ge 0}\gamma^t f(s_t) \Bigm| s_0\Bigr].$$

Discounted sums along the chain are averages under the visitation.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, equation (0.10)
