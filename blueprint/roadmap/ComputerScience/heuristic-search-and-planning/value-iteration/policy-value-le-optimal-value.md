# No deterministic policy beats the optimal value

Let $M$ be a Markov decision process with finitely
many states, finitely many actions (at least one), real rewards $r(s,a)$, and transition
probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over $s'$, and let
$0 \le \gamma < 1$. For every deterministic stationary policy $\pi$, the value $V^\pi$ of $\pi$
is at most the optimal value $V^*$ in every state: $V^\pi(s) \le V^*(s)$ for all states $s$.

The same bound for stationary stochastic policies is [No stochastic policy beats the optimal value](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/stoch-value-le-optimal-value.md).
