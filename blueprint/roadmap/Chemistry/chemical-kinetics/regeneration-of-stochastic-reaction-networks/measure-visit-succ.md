# Probabilities of successive visits multiply by the return probability

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons, $K$ a jump
kernel on $\sigma$ (a probability mass function $K(y, \cdot)$ for each state $y$), and
$x_0, x \in \sigma$. Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps $(\xi_k, E_k)$ are i.i.d. and each map
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$. Count the
visits to $x_0$ of the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$ at steps $n \ge 0$, step $0$ included. For every $k \in \mathbb{N}$,

$$
\mathbb{P}(\text{at least } k + 2 \text{ visits}) =
\mathbb{P}(\text{at least } k + 1 \text{ visits}) \cdot p ,
$$

where $p$ is the probability that the jump chain started at $x_0$ returns to $x_0$ at some step
$n \ge 1$. With the [visits](visit.md) indexed from $0$: visit $k + 1$ happens exactly when visit
$k$ happens and the chain restarted there with the later steps returns to $x_0$. By the
[strong Markov property](measure-inter-shift-at-preimage.md) at visit $k$, the later steps are
independent of what happened before and have the law $\mathbb{P}$ again.
