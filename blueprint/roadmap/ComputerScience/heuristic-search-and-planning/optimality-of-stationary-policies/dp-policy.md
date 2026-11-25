# The dynamic programming policy

Let $M$ be a Markov decision process with finitely many states, a nonempty finite set of actions, rewards and transition probabilities in an ordered field, and a discount factor $\gamma$. For a horizon $N$ and a terminal value $V$, the dynamic programming policy is the Markov policy that at stage $k < N$ acts greedily for the value iterate $T^{N-1-k} V$: it chooses, in each state, an action maximizing $r(s,a) + \gamma \sum_{s'} p(s,a,s')\,(T^{N-1-k} V)(s')$. These are the maximizations of the DP algorithm (minimizations in the cited cost formulation), run backwards from the terminal value.

## Sources

- D. P. Bertsekas, *A Course in Reinforcement Learning*, 2nd ed., Athena Scientific (2026), Section 1.3.1 (the policy $\mu^*_k$ attaining the minimum in the DP algorithm (1.15), written there for costs and stage-dependent data).
