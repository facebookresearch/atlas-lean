# Performance difference lemma for row-stochastic policies

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s, a)$ and transition probabilities $P(s, a, s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. A policy is a row-stochastic matrix $\pi(s, a)$: nonnegative entries, each row summing to $1$. Its value $V^\pi$ is the unique solution of $V^\pi(s) = \sum_a \pi(s, a) \bigl(r(s, a) + \gamma \sum_{s'} P(s, a, s') V^\pi(s')\bigr)$. For all row-stochastic policies $\pi$ and $\pi'$ and every initial weighting
$\mu : S \to \mathbb{R}$,

$$\sum_s \mu(s) V^{\pi'}(s) - \sum_s \mu(s) V^\pi(s) = \frac{1}{1 - \gamma} \sum_{(s, a)} d^{\pi'}_\mu(s, a)\, A^\pi(s, a),$$

where $d^{\pi'}_\mu$ is the discounted state-action occupancy of $\pi'$ from $\mu$ and $A^\pi$ the
advantage of $\pi$. This is [the performance difference lemma](../performance-difference-lemma/performance-difference.md)
with policies given as matrices and an initial weighting in place of an initial state.

## Sources

- S. Kakade and J. Langford, *Approximately Optimal Approximate Reinforcement Learning*, ICML 2002, Lemma 6.1.
- A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and Algorithms*, Lemma 1.16.
