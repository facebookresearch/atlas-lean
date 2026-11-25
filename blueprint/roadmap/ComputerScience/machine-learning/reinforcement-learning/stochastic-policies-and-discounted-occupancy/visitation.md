# Discounted state visitation

Let $P$ be a row-stochastic matrix on a finite set $S$ (nonnegative entries, each row summing to $1$) and let $0 \le \gamma < 1$. The discounted state visitation of the Markov chain $P$ from $s_0$ is

$$d_{s_0}(s) = (1 - \gamma) \sum_{t \ge 0} \gamma^t \Pr(s_t = s \mid s_0) = (1-\gamma)\,\bigl[(I - \gamma P)^{-1}\bigr]_{s_0 s}.$$

It is defined as $1 - \gamma$ times the value of the indicator reward of $s$, and the series form is a theorem.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, equation (0.9)
