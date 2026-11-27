# A discounted MDP as a stochastic shortest path problem

Let $M$ be a Markov decision process with real rewards $r(s,a)$ and transition probabilities $p(s,a,s')$, and let $\gamma$ be a discount factor. The associated stochastic shortest path problem has the same states, actions and rewards, and transition probabilities $\gamma\, p(s,a,s')$ among the states: at every stage the system terminates with probability $1 - \gamma$ and otherwise moves as in $M$.

## Sources

- D. P. Bertsekas, *A Course in Reinforcement Learning*, 2nd ed., Athena Scientific (2026), Section 1.4, item (b) ("introducing an artificial termination state to which the system moves with probability $1 - \alpha$ at every state and stage").
