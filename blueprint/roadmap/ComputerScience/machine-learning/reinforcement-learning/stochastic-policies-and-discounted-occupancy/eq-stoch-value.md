# Uniqueness of the value of a stochastic policy

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. If $V(s) = \sum_a \pi(a \mid s)\bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') V(s')\bigr)$ for every state $s$, then $V = V^\pi$.
