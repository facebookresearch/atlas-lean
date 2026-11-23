# Value of a Markov reward process

Let $P$ be a row-stochastic matrix on a finite set $S$ (nonnegative entries, each row summing to $1$) and let $0 \le \gamma < 1$. The value of the reward $c : S \to \mathbb{R}$ is the unique function $V_c : S \to \mathbb{R}$ with

$$V_c(s) = c(s) + \gamma \sum_{s'} P(s,s')\, V_c(s')\quad\text{for all } s,$$

that is $V_c = (I - \gamma P)^{-1} c$. It exists and is unique because the right-hand side is a $\gamma$-contraction in the sup metric.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Corollary 1.5
