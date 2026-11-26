# A policy's Bellman operator is a contraction

Let $M$ be a Markov decision process with finitely many states $S$, real rewards and stochastic
transition probabilities (nonnegative, each row summing to $1$), let $0 \le \gamma < 1$, and let
$\pi$ be a deterministic stationary policy. Then the [Bellman operator](policy-bellman.md) $T_\pi$
of $\pi$ is a contraction with constant $\gamma$ on the real-valued functions on $S$ with the sup
metric: $\|T_\pi V - T_\pi W\|_\infty \le \gamma \|V - W\|_\infty$ for all $V$ and $W$. Its
unique fixed point is the [value of the policy](policy-value.md) $\pi$.
