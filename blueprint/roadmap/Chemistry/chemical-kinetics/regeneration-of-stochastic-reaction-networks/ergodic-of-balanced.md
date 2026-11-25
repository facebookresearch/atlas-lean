# Balanced law charging $x_0$ and reachability from it give ergodicity

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

Let $w$ be a probability law on $\sigma$, weights $w(y) \in [0, \infty]$ with
$\sum_y w(y) = 1$, that balances the rate-weighted jump kernel,

$$\sum_{y} w(y)\, q(y)\, K(y, z) = w(z)\, q(z) \quad \text{for every } z \in \sigma,$$

with $\sum_y w(y)\, q(y) < \infty$ (sums in $[0, \infty]$). With the self-loops of $K$ included,
this is the stationary master equation $w Q = 0$ of the generator
$Q(y, z) = q(y) (K(y, z) - \mathbf{1}_{y = z})$.

Assume that the chain does not explode from any initial state, let $x_0 \in \sigma$ with
$w(x_0) > 0$, and assume that every state $y$ is reachable from $x_0$ through jumps of positive
probability: there are states $x_0 = u_0, u_1, \dots, u_m = y$ ($m \ge 0$) with
$K(u_{i-1}, u_i) > 0$ for every $i$. Then:

1. the chain started at $x_0$ returns to $x_0$ almost surely: $Y_n = x_0$ for some $n \ge 1$;
2. the mean return time is finite: for the chain started at $x_0$, the time $T_{\tau_1}$ of the
   first return, where $\tau_1$ is the first $n \ge 1$ with $Y_n = x_0$ ($T_{\tau_1} = 0$ if
   there is none), is integrable;
3. for every initial state $x$ and every $f : \sigma \to \mathbb{R}$ with $|f(y)| \le B$ for
   every $y$ (some real $B$), almost surely

$$\frac{1}{t} \int_0^t f(X^x_s)\, ds \to \sum_{y} w(y)\, f(y) \quad (t \to \infty).$$

The sum converges absolutely. Every function on $\sigma$ is measurable, as every subset is. The
return may be a jump from $x_0$ to itself when $K(x_0, x_0) > 0$. Only reachability from $x_0$ is
assumed, not that $x_0$ is reachable from every state.
