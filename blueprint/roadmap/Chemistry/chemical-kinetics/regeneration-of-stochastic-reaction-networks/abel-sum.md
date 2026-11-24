# Abel functional of the jump–hold chain

Let $\sigma$ be a set, $q, g : \sigma \to \mathbb{R}$ real functions (the rates and an
observable), $a \in \mathbb{R}$, $x \in \sigma$ a starting state, and
$\omega = ((\xi_k, E_k))_{k \ge 0}$ a sequence of steps, each a map $\xi_k : \sigma \to \sigma$
and a real clock $E_k$. Let $Y$ be the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$, $Y_0 = x$ and $Y_{k+1} = \xi_k(Y_k)$; let $H_k = E_k / q(Y_k)$ be the
[holding times](../non-explosion-of-stochastic-reaction-networks/holding-time.md), with $H_k = 0$
when $q(Y_k) = 0$; and let $T_k = H_0 + \dots + H_{k-1}$ be the
[jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md), with $T_0 = 0$. The
Abel functional is

$$
A_a g(x, \omega) = \sum_{k=0}^{\infty} g(Y_k)^+ \bigl( e^{-a T_k} (1 - e^{-a H_k}) \bigr)^+
\in [0, \infty],
$$

where $u^+ = \max(u, 0)$: both factors are clamped at $0$, and the series of nonnegative terms is
summed in $[0, \infty]$, where it may be $\infty$. No condition is imposed on $q$, $g$, $a$ or the
clocks.

Before clamping, the second factor is $e^{-a T_k} - e^{-a T_{k+1}}$; it is nonnegative when
$a H_k \ge 0$, for example when $a \ge 0$, the rates are positive and the clocks are nonnegative.
For positive rates, nonnegative clocks, $g \ge 0$, $a > 0$ and jump times tending to $\infty$, the
Abel functional is the Laplace transform $\int_0^\infty a e^{-a t} g(X_t)\, dt$, a lower Lebesgue
integral, of the [path](../non-explosion-of-stochastic-reaction-networks/path.md) $X$ of the
chain started at $x$ (the [Laplace transform identity](lintegral-exp-path-eq-abel-sum.md)).
