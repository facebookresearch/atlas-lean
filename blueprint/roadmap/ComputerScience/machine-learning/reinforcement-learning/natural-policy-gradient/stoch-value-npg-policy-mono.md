# Natural policy gradient never decreases the value

Let $M$ be a Markov decision process with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards $r(s,a)$ and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. For a step size $\eta > 0$ and every state $s$, $t \mapsto V^{\pi_t}(s)$ is nondecreasing.
