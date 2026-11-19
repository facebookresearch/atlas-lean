# The value difference is the value of the averaged advantage

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For stochastic policies $\pi, \pi'$, the difference $V^{\pi'} - V^\pi$ is the value, in the Markov reward process $P^{\pi'}$, of the reward $s \mapsto \sum_a \pi'(a \mid s) A^\pi(s,a)$.
