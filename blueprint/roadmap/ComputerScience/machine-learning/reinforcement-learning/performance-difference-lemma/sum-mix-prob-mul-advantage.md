# Averaged advantage of a mixture

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For $0 \le \alpha \le 1$ and stochastic policies $\pi, \pi'$, the mixture $\pi_\alpha = (1-\alpha)\pi + \alpha\pi'$ satisfies $\sum_a \pi_\alpha(a \mid s) A^\pi(s,a) = \alpha \sum_a \pi'(a \mid s) A^\pi(s,a)$.
