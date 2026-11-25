# Without explosion, states charged by a balanced law are recurrent

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$ (self-loops $K(y, y) > 0$ are allowed).
Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps $(\xi_k, E_k)$, $k \in \mathbb{N}$, are i.i.d.:
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$, and $E_k$ is
an independent exponential clock of rate $1$. Let $q : \sigma \to \mathbb{R}$ be positive rates
($q(y) > 0$ for every $y$), and let $w$ be a probability law on $\sigma$ (weights $w(x) \ge 0$
with $\sum_x w(x) = 1$) that balances the rate-weighted jump kernel,

$$\sum_{x \in \sigma} w(x)\, q(x)\, K(x, y) = w(y)\, q(y) \quad \text{for every } y \in \sigma,$$

with $\sum_x w(x)\, q(x) < \infty$. Assume that from every starting state the
[jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md) tend to $\infty$
$\mathbb{P}$-almost surely. Then every state $x_0$ with $w(x_0) > 0$ is recurrent: the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x_0$ returns to $x_0$, at some step $n \ge 1$, $\mathbb{P}$-almost surely.

Otherwise the return probability would be below $1$, the chain would visit $x_0$ only
[finitely often](ae-exists-visit-eq-top.md) from every state, the fraction of time spent at $x_0$
would [tend to $0$](tendsto-integral-indicator-div-zero.md), and the
[identification of time-average limits](eq-tsum-of-ae-tendsto.md), applied to the indicator of
$x_0$, would give $w(x_0) = 0$.
