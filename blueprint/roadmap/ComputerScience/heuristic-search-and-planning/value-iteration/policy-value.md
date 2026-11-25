# Value of a policy

Let $M$ be a Markov decision process with a finite set of states $S$,
a set of actions $A$, real rewards $r(s,a)$, and transition probabilities $P(s,a,s')$ that are
nonnegative and sum to $1$ over $s'$, let $0 \le \gamma < 1$, and let $\pi : S \to A$ be a
deterministic stationary policy. The value of $\pi$ is the unique function
$V^\pi : S \to \mathbb{R}$ that is a fixed point of the Bellman operator of $\pi$, that is,
$V^\pi(s) = r(s,\pi(s)) + \gamma \sum_{s'} P(s,\pi(s),s') \, V^\pi(s')$ for every state $s$.
It exists and is unique because this operator is a $\gamma$-contraction in the sup metric.
