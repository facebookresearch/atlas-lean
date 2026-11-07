# Away from optimality, improvement changes the value

Let $M$ be a Markov decision process
with a finite set of states $S$, a finite nonempty set of actions $A$, real rewards and stochastic
transition probabilities, and let $0 \le \gamma < 1$. Write $V^\pi$ for the value of a
deterministic policy $\pi : S \to A$ and $V^*$ for the optimal value. If $V^\pi \ne V^*$, then the
improved policy $\pi'$ satisfies $V^{\pi'} \ne V^\pi$ (as functions on $S$).
