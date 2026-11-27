# Occupation integral up to the $m$-th jump time equals the reward

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons,
$q : \sigma \to \mathbb{R}$ positive rates ($q(y) > 0$ for every $y$), $x \in \sigma$, and
$\omega = ((\xi_k, E_k))_{k \ge 0}$ a sequence of steps (maps $\xi_k : \sigma \to \sigma$ and real
clocks $E_k$) with nonnegative clocks, $E_k \ge 0$ for every $k$, such that the
[path](../non-explosion-of-stochastic-reaction-networks/path.md) $s \mapsto X_s$ of the chain
started at $x$ is measurable. Let $g : \sigma \to \mathbb{R}$ be bounded: $|g(y)| \le B$ for every
$y$. Then for every $m \in \mathbb{N}$,

$$\int_0^{T_m} g(X_s)\, ds = \sum_{k < m} g(Y_k)\, H_k ,$$

the [reward](reward.md) of $g$ over the first $m$ holding intervals. Here $Y$ is the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$, $H_k = E_k / q(Y_k) \ge 0$ are the
[holding times](../non-explosion-of-stochastic-reaction-networks/holding-time.md), and
$T_m = H_0 + \dots + H_{m-1} \ge 0$ is the $m$-th
[jump time](../non-explosion-of-stochastic-reaction-networks/jump-time.md). On each interval
$[T_k, T_{k+1})$, of length $H_k$, the path is at $Y_k$. With positive rates and nonnegative
clocks, the path is measurable for instance when the jump times tend to $\infty$.
