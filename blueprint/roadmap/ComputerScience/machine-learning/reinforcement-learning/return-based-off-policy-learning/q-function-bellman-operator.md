# Q-function Bellman operator of a stochastic policy

For a stochastic policy $\pi$, the operator $P^\pi$ averages a Q-function over the next state and the policy's next action, and the Bellman operator $T^\pi Q = r + \gamma P^\pi Q$ is defined on Q-functions rather than on state values.

Let $M$ be a Markov decision process with a finite set of states $X$, a finite nonempty set of actions $A$, real rewards $r(x,a)$ and transition probabilities $P(x' \mid x,a)$ that are nonnegative and sum to $1$ over $x'$, and let $0 \le \gamma < 1$. A Q-function is a map $Q : X \times A \to \mathbb{R}$; the reward $r$ is one. For a stochastic policy $\pi$ and a Q-function $Q$, write $(\mathbb{E}_\pi Q)(x') = \sum_{a' \in A} \pi(a' \mid x')\, Q(x',a')$ and define

$$(P^\pi Q)(x,a) = \sum_{x' \in X} \sum_{a' \in A} P(x' \mid x,a)\, \pi(a' \mid x')\, Q(x',a') = \sum_{x' \in X} P(x' \mid x,a)\, (\mathbb{E}_\pi Q)(x'),$$

$$T^\pi Q = r + \gamma P^\pi Q .$$

As a matrix indexed by state–action pairs, $P^\pi$ has the nonnegative entries $P(x' \mid x,a)\,\pi(a' \mid x')$ and every row sums to $1$: it is the transition matrix of the chain that moves by $P$ and then draws the next action from $\pi$. Throughout this topic $\|Q\| = \max_{x,a} |Q(x,a)|$ is the sup norm, $e$ is the Q-function equal to $1$ everywhere, and an inequality between Q-functions is meant at every pair.

The operator of [Bellman operator of a policy](../../../heuristic-search-and-planning/value-iteration/policy-bellman.md) is a different object: it acts on state values and takes a deterministic policy.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Stochastic Markov decision process](../../../heuristic-search-and-planning/value-iteration/stochastic.md)
- [Stochastic policy](../stochastic-policies-and-discounted-occupancy/stochastic-policy.md)

## Proof depends on

None.

## Expansion

A definition. The two expressions for $P^\pi Q$ agree by summing over $a'$ first. Nonnegativity of the entries comes from that of $P$ and $\pi$, and the row sums equal $\sum_{x'} P(x' \mid x,a) \sum_{a'} \pi(a' \mid x') = 1$.

## Sources

- R. Munos, T. Stepleton, A. Harutyunyan, M. G. Bellemare, *Safe and Efficient Off-Policy Reinforcement Learning*, Advances in Neural Information Processing Systems 29 (NIPS 2016), arXiv:1606.02647v2, <https://arxiv.org/abs/1606.02647v2>: Section 1 (definitions of $P^\pi$ and of the Bellman operator $T^\pi$), Section 2 (notation $\mathbb{E}_\pi Q$).
