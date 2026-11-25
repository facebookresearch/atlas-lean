# Average-reward optimality equation

Let $M$ be a finite Markov decision process with state set $S$, action set $A$, rewards $r(s,a)$ and
transition probabilities $P(s' \mid s,a)$, and suppose $M$ is strongly connected. Then there exist
$\rho \in \mathbb{R}$ and $v : S \to \mathbb{R}$ such that for every $s \in S$

$$\rho + v(s) = \max_{a \in A}\Big[r(s,a) + \sum_{s'} P(s' \mid s,a)\, v(s')\Big].$$

For any such pair, $\rho = \rho^*$ is the optimal long-run average reward from every starting state,
and every policy that is greedy with respect to $v$ is optimal.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Long-run average reward of a history-dependent policy in a finite MDP (the lim inf of the expected average reward over the first T steps), average-reward optimality, and strongly connected (communicating) MDPs.

## Depends on

- [History-dependent randomized policies and trajectory laws](history-dependent-randomized-policies-and-trajectory-laws.md)

## Proof depends on

- [Bellman's operator is a contraction](../value-iteration/bellman-contracting.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Theorem 38.2. <https://tor-lattimore.com/downloads/book/book.pdf>
