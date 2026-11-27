# A policy has zero average advantage over itself

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For every stochastic policy $\pi$ and state $s$, $\sum_a \pi(a \mid s)\, A^\pi(s,a) = 0$.
