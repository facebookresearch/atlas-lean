# Averaged advantage as a Bellman residual

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For stochastic policies $\pi, \pi'$ and a state $s$,

$$\sum_a \pi'(a \mid s)\, A^\pi(s,a) = r^{\pi'}(s) + \gamma \sum_{s'} P^{\pi'}(s,s')\, V^\pi(s') - V^\pi(s).$$
