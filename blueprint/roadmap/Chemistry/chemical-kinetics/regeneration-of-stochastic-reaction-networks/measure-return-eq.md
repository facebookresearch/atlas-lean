# Return probability to $x_0$ as an average of hitting probabilities

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons, $K$ a jump
kernel on $\sigma$ (a probability mass function $K(y, \cdot)$ for each state $y$), and
$x_0 \in \sigma$. Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps $(\xi_k, E_k)$ are i.i.d. and each map
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$. The
probability that the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x_0$ returns to $x_0$, that is, $Y_n = x_0$ for some step $n \ge 1$ (its
[visit](visit.md) of index $1$ exists), is

$$\mathbb{P}\bigl(\exists n \ge 1,\ Y_n = x_0\bigr) = \sum_{y \in \sigma} K(x_0, y)\, h(y),$$

where $h(y)$ is the [hitting probability](hit-prob.md) of $x_0$ from $y$: the probability that the
jump chain started at $y$ ever visits $x_0$, step $0$ included.
