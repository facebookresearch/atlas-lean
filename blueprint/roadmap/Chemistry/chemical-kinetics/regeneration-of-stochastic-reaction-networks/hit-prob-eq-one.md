# A recurrent state is hit almost surely from every state it reaches

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons, $K$ a jump
kernel on $\sigma$ (a probability mass function $K(y, \cdot)$ for each state $y$), and
$\mathbb{P}$ the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md),
a probability measure under which the steps $(\xi_k, E_k)$ are i.i.d. and each map
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$.
Let $x_0$ be recurrent: the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x_0$ returns to $x_0$, at some step $n \ge 1$, $\mathbb{P}$-almost surely. Let $y$ be
reachable from $x_0$: there are states $x_0 = u_0, u_1, \dots, u_m = y$, with $m \ge 0$, such that
$K(u_i, u_{i+1}) > 0$ for every $i < m$. Then the jump chain started at $y$ visits $x_0$ almost
surely: the [hitting probability](hit-prob.md) of $x_0$ from $y$ is $1$. In particular, if every
state is reachable from $x_0$, the chain hits $x_0$ almost surely from every starting state.
