# The discounted state occupancy is a probability distribution

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For every stochastic policy $\pi$ and state $s_0$, $\sum_s d^\pi_{s_0}(s) = 1$.
