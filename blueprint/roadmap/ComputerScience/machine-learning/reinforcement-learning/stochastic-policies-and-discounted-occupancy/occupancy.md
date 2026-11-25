# Discounted state-action occupancy of a row-stochastic policy

Let $M$ be a Markov decision process with a finite set of states $S$, a finite set of actions $A$, real rewards $r(s, a)$ and transition probabilities $P(s, a, s')$ that are nonnegative and sum to $1$ over $s'$, and let $0 \le \gamma < 1$. A policy is a row-stochastic matrix $\pi(s, a)$: nonnegative entries, each row summing to $1$. Its value $V^\pi$ is the unique solution of $V^\pi(s) = \sum_a \pi(s, a) \bigl(r(s, a) + \gamma \sum_{s'} P(s, a, s') V^\pi(s')\bigr)$. For an initial weighting $\mu : S \to \mathbb{R}$, the discounted state-action
occupancy is $d^\pi_\mu(s, a) = d_\mu(s)\, \pi(s, a)$, where

$$d_\mu(s) = (1 - \gamma) \sum_{s_0} \mu(s_0)\, W_s(s_0)$$

and $W_s$ is the unique solution of $W_s = \mathbf{1}_s + \gamma P^\pi W_s$, with
$P^\pi(s, s') = \sum_a \pi(s, a) P(s, a, s')$ and $\mathbf{1}_s$ the indicator of $s$; equivalently
$W_s(s_0) = \sum_{t \ge 0} \gamma^t \bigl[(P^\pi)^t\bigr]_{s_0 s}$. When $\mu$ is an initial
distribution (nonnegative, summing to $1$), $d^\pi_\mu(s, a) = (1 - \gamma) \sum_t \gamma^t
\Pr(S_t = s, A_t = a)$ for the chain started from $\mu$. It is a state-action form, with the policy
given as a matrix, of [the discounted state occupancy of a policy](../performance-difference-lemma/occupancy.md).
