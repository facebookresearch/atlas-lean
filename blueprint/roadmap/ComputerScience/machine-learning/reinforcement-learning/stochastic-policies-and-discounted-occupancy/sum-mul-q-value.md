# Action-weighted sum of action values

Let $M$ be a Markov decision process with rewards $r(s, a)$ and transition weights $P(s, a, s')$, let $\gamma$ be a discount factor, $V : S \to \mathbb{R}$ a value function and $\pi : S \to A \to \mathbb{R}$ any matrix of action weights. For every state $s$,

$$\sum_a \pi(s, a)\, Q(s, a) = r^\pi(s) + \gamma \sum_{s'} P^\pi(s, s')\, V(s'),$$

where $Q(s, a) = r(s, a) + \gamma \sum_{s'} P(s, a, s') V(s')$, $r^\pi(s) = \sum_a \pi(s, a) r(s, a)$ and $P^\pi(s, s') = \sum_a \pi(s, a) P(s, a, s')$. The identity is algebraic: the weights $\pi(s, a)$ need not be nonnegative or sum to $1$. For a stochastic policy $\pi$ the left side is the policy average of the action values.
