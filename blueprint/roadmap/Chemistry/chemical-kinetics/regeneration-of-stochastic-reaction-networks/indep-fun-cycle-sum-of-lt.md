# If all visits are almost sure, distinct cycle rewards are independent

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$ (self-loops $K(y, y) > 0$ are allowed).
Under the [law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md) $\mathbb{P}$ the steps
$\omega_n = (\xi_n, E_n)$, $n \in \mathbb{N}$, are i.i.d.: $\xi_n : \sigma \to \sigma$ has
independent coordinates $\xi_n(y) \sim K(y, \cdot)$, and $E_n$ is an independent exponential
clock of rate $1$. The [jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md) started at $x$ is
$Y_0 = x$, $Y_{n+1} = \xi_n(Y_n)$.

For states $x_0, x$ let $\tau_0 < \tau_1 < \cdots$ be the steps of the successive
[visits](visit.md) to $x_0$ of the jump chain $Y$ started at $x$ ($\tau_k$ is the step $n$ with
$Y_n = x_0$ and exactly $k$ earlier visits, and $\tau_k = \infty$ if there are at most $k$
visits).
For $q, g : \sigma \to \mathbb{R}$ write $H_i = E_i / q(Y_i)$ for the holding times, with the
convention $E / 0 = 0$ (the functions $q$ and $g$ are arbitrary; in the chain $q > 0$ is the
vector of exit rates), and $R(m) = \sum_{i < m} g(Y_i) H_i$ for the [reward](reward.md)
collected by $g$ in the first $m$ steps; a missing visit, $\tau = \infty$, counts as step $0$ in
$R(\tau)$. The reward of the $k$-th [regeneration cycle](cycle-sum.md) is
$C_k(g) = R(\tau_{k+1}) - R(\tau_k)$, that is $\sum_{\tau_k \le i < \tau_{k+1}} g(Y_i) H_i$ when
both visits happen.

Suppose that almost surely every visit happens: $\tau_k < \infty$ for every $k$, almost surely.
Then for any $q, g, g' : \sigma \to \mathbb{R}$ and $j < k$, the reward $C_j(g)$ collected by
$g$ in the $j$-th cycle and the reward $C_k(g')$ collected by $g'$ in the $k$-th cycle are
independent under $\mathbb{P}$. This is the strong Markov property at the visit $\tau_k$: the
steps from $\tau_k$ on are independent of everything determined before $\tau_k$.
