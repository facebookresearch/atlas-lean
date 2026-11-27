# A policy's Bellman operator is monotone

Let $M$ be a Markov decision process with finitely many states, and with rewards $r(s, a)$ and
stochastic transition probabilities $p(s, a, s')$ (nonnegative, each row summing to $1$) in a
linearly ordered field $K$, and let $\gamma \ge 0$ in $K$. Let $\pi$ be a deterministic stationary policy with
[Bellman operator](policy-bellman.md) $T_\pi$. If two value estimates satisfy $V \le W$ pointwise,
then $T_\pi V \le T_\pi W$ pointwise.
