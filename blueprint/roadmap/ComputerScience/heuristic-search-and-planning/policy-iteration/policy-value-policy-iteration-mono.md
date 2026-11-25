# Policy iteration never decreases the value

Let $M$ be a Markov decision process with a
finite set of states $S$, a finite nonempty set of actions $A$, real rewards and stochastic
transition probabilities, and let $0 \le \gamma < 1$. Write $V^\pi$ for the value of a
deterministic policy $\pi : S \to A$, and $\pi_k$ for the policy after $k$ steps of policy
iteration from $\pi$. If $i \le j$, then $V^{\pi_i}(s) \le V^{\pi_j}(s)$ for every state $s$.
