# Advantage function of a row-stochastic policy

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s, a)$ and transition probabilities $P(s, a, s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. A policy is a row-stochastic matrix $\pi(s, a)$: nonnegative entries, each row summing to $1$. Its value $V^\pi$ is the unique solution of $V^\pi(s) = \sum_a \pi(s, a) \bigl(r(s, a) + \gamma \sum_{s'} P(s, a, s') V^\pi(s')\bigr)$. The advantage of action $a$ in state $s$ is

$$A^\pi(s, a) = Q^\pi(s, a) - V^\pi(s), \qquad Q^\pi(s, a) = r(s, a) + \gamma \sum_{s'} P(s, a, s') V^\pi(s') .$$

This is the [advantage function](../performance-difference-lemma/advantage.md) with the policy given as a
row-stochastic matrix.
