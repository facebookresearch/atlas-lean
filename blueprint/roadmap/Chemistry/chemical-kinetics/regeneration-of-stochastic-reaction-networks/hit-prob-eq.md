# Hitting probabilities satisfy the first-step equation off the target

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons, $K$ a jump
kernel on $\sigma$ (a probability mass function $K(y, \cdot)$ for each state $y$), and
$x_0 \in \sigma$. Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps $(\xi_k, E_k)$ are i.i.d. and each map
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$. Let $h(y)$ be
the [hitting probability](hit-prob.md) of $x_0$ from $y$: the probability that the jump chain
$Y_0 = y$, $Y_{k+1} = \xi_k(Y_k)$ ever visits $x_0$, step $0$ included. For every state
$x \ne x_0$,

$$h(x) = \sum_{y \in \sigma} K(x, y)\, h(y) .$$

The condition $x \ne x_0$ is needed: $h(x_0) = 1$, while $\sum_y K(x_0, y)\, h(y)$ is the
[return probability](measure-return-eq.md) to $x_0$, which can be smaller than $1$.
