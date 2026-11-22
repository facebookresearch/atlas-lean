# Policy improvement theorem

Let $M$ be a Markov decision process with a finite set of
states $S$, a finite nonempty set of actions $A$, real rewards and stochastic transition
probabilities, and let $0 \le \gamma < 1$. Write $V^\pi$ for the value of a deterministic policy
$\pi : S \to A$. For every deterministic policy $\pi$, the improved policy $\pi'$, which is greedy
for $V^\pi$, satisfies $V^\pi(s) \le V^{\pi'}(s)$ for every state $s$.
