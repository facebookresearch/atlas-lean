# Optimal value of a discounted Markov decision process

Let $M$ be a Markov decision
process with finitely many states $S$, finitely many actions (at least one), real rewards
$r(s,a)$, and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over
$s'$, and let $0 \le \gamma < 1$. The optimal value of $M$ with discount $\gamma$ is the unique
function $V^* : S \to \mathbb{R}$ that is a fixed point of the Bellman optimality operator, that
is, $V^*(s) = \max_a \bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V^*(s')\bigr)$ for every
state $s$. It exists and is unique because this operator is a $\gamma$-contraction in the sup
metric.

It is the largest value of any stationary policy: deterministic policies are covered by [No deterministic policy beats the optimal value](policy-value-le-optimal-value.md) and [A greedy policy for the optimal value is optimal](policy-value-greedy.md), stochastic ones by [No stochastic policy beats the optimal value](../../machine-learning/reinforcement-learning/stochastic-policies-and-discounted-occupancy/stoch-value-le-optimal-value.md). Non-stationary deterministic Markov policies are covered by [Optimality of stationary policies](../optimality-of-stationary-policies/is-greatest-markov-value.md). Optimality among all randomized, possibly history-dependent policies is Theorem 1.7 of Agarwal, Jiang, Kakade and Sun, *Reinforcement Learning: Theory and Algorithms*.
