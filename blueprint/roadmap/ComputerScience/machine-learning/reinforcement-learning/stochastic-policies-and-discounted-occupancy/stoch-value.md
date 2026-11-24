# Value of a stochastic policy

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. The value $V^\pi$ of a stochastic policy $\pi$ is the value of the Markov reward process $(P^\pi, r^\pi)$: the unique solution of $V^\pi = r^\pi + \gamma P^\pi V^\pi$, that is the expected discounted return $\mathbb{E}[\sum_t \gamma^t r(s_t, a_t) \mid s_0 = s]$ with $a_t \sim \pi(\cdot \mid s_t)$.

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Section 1.1.1 and Corollary 1.5
