# A return probability below 1 gives finitely many visits almost surely

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons, $K$ a jump
kernel on $\sigma$ (a probability mass function $K(y, \cdot)$ for each state $y$), and
$\mathbb{P}$ the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md),
a probability measure under which the steps $(\xi_k, E_k)$ are i.i.d. and each map
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$. Let
$x_0 \in \sigma$ be such that the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x_0$ returns to $x_0$, at some step $n \ge 1$, with probability $p < 1$. Then for
every starting state $x$, $\mathbb{P}$-almost surely the jump chain started at $x$ visits $x_0$
only finitely many times: some [visit](visit.md) index $k$ is never reached. Indeed, by the
[product formula for successive visits](measure-visit-succ.md), the probability of at least
$k + 1$ visits is at most $p^k$, which tends to $0$.
