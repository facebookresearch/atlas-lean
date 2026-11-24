# Reward of an observable over the first $m$ holding times

Let $S$ be a set, $q, g : S \to \mathbb{R}$ any real functions, $x \in S$, $\omega$ a step
sequence with $\omega_i = (\xi_i, E_i)$, $\xi_i : S \to S$ and $E_i \in \mathbb{R}$, and
$m \in \mathbb{N}$. Let $Y$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$ and $H_i = E_i / q(Y_i)$ its
[holding times](../non-explosion-of-stochastic-reaction-networks/holding-time.md).
The reward collected by the observable $g$ during the first $m$ holding intervals is

$$R_m(x, \omega) = \sum_{i < m} g(Y_i)\, H_i ,$$

with $R_0 = 0$. By the convention $a / 0 = 0$, a step at a state with $q(Y_i) = 0$ has $H_i = 0$
and contributes $0$, not the infinite stay at an absorbing state. For $g = 1$ it is the sum
$H_0 + \dots + H_{m-1}$ that defines the
[jump time](../non-explosion-of-stochastic-reaction-networks/jump-time.md) $T_m$.
In the model $q$ is a positive holding rate and the clocks $E_i$ are nonnegative, so that $H_i$ is
the time spent in $Y_i$; the definition allows any real $q$, $g$ and clock values. On a countable
state space whose singletons are measurable, for positive rates, nonnegative clocks and a bounded
$g$, $R_m$ is the
[integral of $g$ along the path up to the jump time $T_m$](integral-path-jump-time.md), when the
path is measurable in time.
