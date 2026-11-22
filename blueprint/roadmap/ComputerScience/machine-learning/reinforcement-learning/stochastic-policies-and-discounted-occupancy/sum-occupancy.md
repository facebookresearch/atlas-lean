# Total mass of the state-action occupancy of a row-stochastic policy

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s, a)$ and transition probabilities $P(s, a, s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. A policy is a row-stochastic matrix $\pi(s, a)$: nonnegative entries, each row summing to $1$. Its value $V^\pi$ is the unique solution of $V^\pi(s) = \sum_a \pi(s, a) \bigl(r(s, a) + \gamma \sum_{s'} P(s, a, s') V^\pi(s')\bigr)$. If the initial weighting $\mu : S \to \mathbb{R}$ satisfies $\sum_s \mu(s) = 1$, then
the discounted state-action occupancy $d^\pi_\mu$ has total mass $\sum_{(s, a)} d^\pi_\mu(s, a) = 1$.
No sign condition on $\mu$ is assumed, so $d^\pi_\mu$ need not be a probability distribution; its
entries are nonnegative when $\mu$ is nonnegative. This is the counterpart, with the policy given as
a matrix, of [the total mass of the discounted state occupancy](../performance-difference-lemma/sum-occupancy.md).
