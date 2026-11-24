# Improvement stalls exactly at optimal policies

Let $M$ be a Markov decision process with a
finite set of states $S$, a finite nonempty set of actions $A$, real rewards and stochastic
transition probabilities, and let $0 \le \gamma < 1$. Write $V^\pi$ for the value of a
deterministic policy $\pi : S \to A$ and $V^*$ for the optimal value. For every deterministic
policy $\pi$, with improved policy $\pi'$, we have $V^{\pi'} = V^\pi$ if and only if
$V^\pi = V^*$ (as functions on $S$).
