# Non-explosive path, finitely many visits: zero time fraction at $x_0$

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons,
$q : \sigma \to \mathbb{R}$ positive rates ($q(y) > 0$ for every $y$), $x_0, x \in \sigma$, and
$\omega = ((\xi_k, E_k))_{k \ge 0}$ a sequence of steps (maps $\xi_k : \sigma \to \sigma$ and real
clocks $E_k$) with nonnegative clocks, $E_k \ge 0$ for every $k$, whose
[jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md) tend to $\infty$.
Suppose that the
[jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md)
started at $x$ visits $x_0$ at most $k_0$ times, for some $k_0 \in \mathbb{N}$ (its
[visit](visit.md) of index $k_0$ does not exist). Then the fraction of time that the
[path](../non-explosion-of-stochastic-reaction-networks/path.md) $X$ spends at $x_0$ tends to $0$:

$$\frac{1}{t} \int_0^t \mathbf{1}_{\{X_s = x_0\}}\, ds \to 0 \quad \text{as } t \to \infty .$$

The time spent at $x_0$ is at most the total holding time of the finitely many visits, since after
the last visit the path does not return to $x_0$. The statement concerns one step sequence; no
probability is involved.
