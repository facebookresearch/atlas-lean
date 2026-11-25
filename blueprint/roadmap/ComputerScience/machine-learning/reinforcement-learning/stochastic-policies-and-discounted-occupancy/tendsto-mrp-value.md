# The value is the discounted sum of expected rewards

Let $P$ be a row-stochastic matrix on a finite set $S$ (nonnegative entries, each row summing to $1$) and let $0 \le \gamma < 1$. For every reward $c$, the partial sums $\sum_{t < n} \gamma^t P^t c$ converge to $V_c$ as $n \to \infty$. Thus $V_c(s) = \mathbb{E}\bigl[\sum_{t \ge 0} \gamma^t c(s_t) \mid s_0 = s\bigr]$ for the Markov chain with transition matrix $P$.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Corollary 1.5 and Lemma 1.6
