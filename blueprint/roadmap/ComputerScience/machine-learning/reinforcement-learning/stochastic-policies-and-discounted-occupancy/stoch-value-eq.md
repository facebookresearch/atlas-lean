# Bellman consistency for stochastic policies

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For every stochastic policy $\pi$ and state $s$,

$$V^\pi(s) = \sum_a \pi(a \mid s)\Bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s')\, V^\pi(s')\Bigr) = \sum_a \pi(a\mid s)\, Q^\pi(s,a).$$

## Sources

- A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and Algorithms*, https://rltheorybook.github.io/rltheorybook_AJKS_V3.pdf, Lemma 1.4
