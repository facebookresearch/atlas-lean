# Value bound

Let $P$ be a row-stochastic matrix on a finite set $S$ (nonnegative entries, each row summing to $1$) and let $0 \le \gamma < 1$. If $|c(s)| \le C$ for every state $s$, then $|V_c(s)| \le C / (1 - \gamma)$ for every state $s$; equivalently $\|(I - \gamma P)^{-1} c\|_\infty \le \|c\|_\infty / (1 - \gamma)$.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 2.3
