# Policy improvement step

Let $M$ be a Markov decision process with a finite set of states
$S$, a finite nonempty set of actions $A$, real rewards $r(s, a)$ and stochastic transition
probabilities $P(s' \mid s, a)$, and let $0 \le \gamma < 1$. The improvement of a deterministic
policy $\pi : S \to A$ is a fixed choice of policy greedy for the value $V^\pi$ of $\pi$: in each
state $s$ it takes a chosen action $a$ maximizing
$r(s, a) + \gamma \sum_{s'} P(s' \mid s, a) V^\pi(s')$ over $A$ (ties broken arbitrarily).
