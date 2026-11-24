# Renewal–reward when all visits to a positive recurrent state happen

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$ (self-loops $K(y, y) > 0$ are allowed).
Under the [law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md) $\mathbb{P}$ the steps
$\omega_n = (\xi_n, E_n)$, $n \in \mathbb{N}$, are i.i.d.: $\xi_n : \sigma \to \sigma$ has
independent coordinates $\xi_n(y) \sim K(y, \cdot)$, and $E_n$ is an independent exponential
clock of rate $1$. The [jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md) started at $x$ is
$Y_0 = x$, $Y_{n+1} = \xi_n(Y_n)$.
For positive rates $q : \sigma \to \mathbb{R}$, $q(y) > 0$ for every $y$, the chain started at $x$
has holding times $H_n = E_n / q(Y_n)$, [jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md)
$T_n = H_0 + \cdots + H_{n-1}$ and [path](../non-explosion-of-stochastic-reaction-networks/path.md) $X^x_s = Y_n$ for
$T_n \le s < T_{n+1}$. Non-explosion from $x$ means that almost surely $T_n \to \infty$.

Let $g : \sigma \to \mathbb{R}$ with $|g(y)| \le 1$ for every $y$, and $x_0, x \in \sigma$.
Write $\tau'_1$ for the step of the first return to $x_0$ of the chain started at $x_0$,
$R_g = \sum_{i < \tau'_1} g(Y'_i) H'_i$ for the [reward](return-reward.md) collected by $g$ during
that first excursion, and $R_1 = T'_{\tau'_1}$ for the return time (both $0$ if there is no
return). Assume:

- the chain started at $x$ does not explode;
- almost surely the chain started at $x$ visits $x_0$ infinitely often: every
  [visit](visit.md) $\tau_k$, $k \in \mathbb{N}$, happens;
- the chain started at $x_0$ returns to $x_0$ almost surely;
- the mean return time is finite: $R_1$ is integrable.

Then almost surely

$$\frac{1}{t} \int_0^t g(X^x_s)\, ds \to \frac{\mathbb{E}[R_g]}{\mathbb{E}[R_1]} \quad
(t \to \infty).$$

Both expectations are finite, as $|R_g| \le R_1$ almost surely, and $\mathbb{E}[R_1] > 0$, since
the return time is at least the first holding time $E_0 / q(x_0) > 0$. The return may be a jump
from $x_0$ to itself when $K(x_0, x_0) > 0$.
