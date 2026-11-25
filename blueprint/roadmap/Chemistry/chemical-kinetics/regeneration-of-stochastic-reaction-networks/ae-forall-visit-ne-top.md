# A recurrent state reaching all states is visited infinitely often a.s.

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons, $K$ a jump
kernel on $\sigma$ (a probability mass function $K(y, \cdot)$ for each state $y$), and
$\mathbb{P}$ the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md),
a probability measure under which the steps $(\xi_k, E_k)$ are i.i.d. and each map
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$.
Let $x_0$ be recurrent, meaning that the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x_0$ returns to $x_0$, at some step $n \ge 1$, $\mathbb{P}$-almost surely, and let
every state $y$ be reachable from $x_0$: there are states $x_0 = u_0, u_1, \dots, u_m = y$, with
$m \ge 0$, such that $K(u_i, u_{i+1}) > 0$ for every $i < m$. Then for every starting state $x$,
$\mathbb{P}$-almost surely the jump chain started at $x$ visits $x_0$ infinitely often: every
[visit](visit.md) index $k$ is reached. The first visit happens almost surely by
[hitting from reachable states](hit-prob-eq-one.md), and the
[product formula for successive visits](measure-visit-succ.md), with return probability $1$,
gives every further visit probability $1$.
