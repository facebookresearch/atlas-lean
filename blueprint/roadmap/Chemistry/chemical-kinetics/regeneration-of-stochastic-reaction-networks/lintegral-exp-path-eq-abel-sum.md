# The Abel functional is the Laplace transform of a non-explosive path

Let $\sigma$ be a set, $q : \sigma \to \mathbb{R}$ positive rates ($q(y) > 0$ for every $y$),
$x \in \sigma$, and $\omega = ((\xi_k, E_k))_{k \ge 0}$ a sequence of steps (maps
$\xi_k : \sigma \to \sigma$ and real clocks $E_k$) with nonnegative clocks, $E_k \ge 0$ for every
$k$, whose [jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md) $T_k$ tend
to $\infty$ (no explosion). Let $g : \sigma \to \mathbb{R}$ be nonnegative and $a > 0$. Then the
[Abel functional](abel-sum.md) is the Laplace transform of the observed
[path](../non-explosion-of-stochastic-reaction-networks/path.md) $X$ of the chain started at $x$:

$$
\int_0^\infty a e^{-a t} g(X_t)\, dt = \sum_{k=0}^{\infty} g(Y_k)\, e^{-a T_k}
\bigl( 1 - e^{-a H_k} \bigr) = A_a g(x, \omega),
$$

where the integral is the lower Lebesgue integral over $(0, \infty)$, both sides lie in
$[0, \infty]$, $Y$ is the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$ and $H_k = E_k / q(Y_k)$ are the holding times. The path is at $Y_k$ on
$[T_k, T_{k+1})$, these intervals cover $[0, \infty)$ because the jump times tend to $\infty$, and
$\int_{T_k}^{T_{k+1}} a e^{-a t}\, dt = e^{-a T_k} (1 - e^{-a H_k})$.
