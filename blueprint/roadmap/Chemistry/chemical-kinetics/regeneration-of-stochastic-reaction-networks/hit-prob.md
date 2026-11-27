# Probability that the jump chain ever visits a given state

Let $\sigma$ be a measurable space and $K$ a jump kernel on $\sigma$: a probability mass function
$K(y, \cdot)$ on $\sigma$ for each state $y$. Let $\mathbb{P}$ be the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\omega = ((\xi_n, E_n))_{n \ge 0}$, a probability measure under which the steps are i.i.d., each
$\xi_n : \sigma \to \sigma$ having independent coordinates $\xi_n(y) \sim K(y, \cdot)$ (the clocks
$E_n$, independent exponential variables of rate $1$, play no role here). For states
$x_0$ and $x$, the hitting probability of $x_0$ from $x$ is

$$h(x) = \mathbb{P}\bigl(\exists n \ge 0,\ Y_n = x_0\bigr) \in [0, 1],$$

where $Y_0 = x$, $Y_{n+1} = \xi_n(Y_n)$ is the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$: the probability that the chain ever visits $x_0$. Step $n = 0$ counts, so
$h(x_0) = 1$. If the event is not measurable, $h(x)$ is its outer measure.
