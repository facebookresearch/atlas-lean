# Optimal value of a discounted Markov decision process

Let $M$ be a Markov decision
process with finitely many states $S$, finitely many actions (at least one), real rewards
$r(s,a)$, and transition probabilities $P(s,a,s')$ that are nonnegative and sum to $1$ over
$s'$, and let $0 \le \gamma < 1$. The optimal value of $M$ with discount $\gamma$ is the unique
function $V^* : S \to \mathbb{R}$ that is a fixed point of the Bellman optimality operator, that
is, $V^*(s) = \max_a \bigl(r(s,a) + \gamma \sum_{s'} P(s,a,s') \, V^*(s')\bigr)$ for every
state $s$. It exists and is unique because this operator is a $\gamma$-contraction in the sup
metric.
