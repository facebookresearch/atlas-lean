# First-step decomposition of the Abel functional

Let $\sigma$ be a set, $q, g : \sigma \to \mathbb{R}$, $a \in \mathbb{R}$, $x \in \sigma$, and
$\omega = ((\xi_k, E_k))_{k \ge 0}$ a sequence of steps, each a map $\xi_k : \sigma \to \sigma$
and a real clock $E_k$. The [Abel functional](abel-sum.md) $A_a g$ satisfies

$$
A_a g(x, \omega) = g(x)^+ \bigl( 1 - e^{-a H_0} \bigr)^+ + e^{-a H_0}\,
A_a g(\xi_0(x), \theta_1 \omega),
$$

an identity in $[0, \infty]$, where $u^+ = \max(u, 0)$, $H_0 = E_0 / q(x)$ is the first holding
time ($H_0 = 0$ when $q(x) = 0$), and $\theta_1 \omega = ((\xi_{k+1}, E_{k+1}))_{k \ge 0}$ is the
[shifted step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md).
No condition is imposed on $q$, $g$, $a$ or the clocks. The first summand is the term $k = 0$ of
the series. The other terms are those of the chain restarted at $\xi_0(x)$ with the shifted
steps, each multiplied by $e^{-a H_0}$, because the jump times satisfy $T_{k+1} = H_0 + T'_k$,
where $T'_k$ are the jump times of the restarted chain.
