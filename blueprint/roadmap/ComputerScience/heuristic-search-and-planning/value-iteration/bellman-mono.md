# The Bellman optimality operator is monotone

Let $M$ be a Markov decision process with finitely many states, a nonempty finite set of actions,
and rewards and stochastic transition probabilities (nonnegative, each row summing to $1$) in a
linearly ordered field $K$, and let $\gamma \ge 0$ in $K$. If two value estimates satisfy
$V \le W$ pointwise, then the [Bellman optimality operator](bellman.md) $T$ satisfies
$TV \le TW$ pointwise.
