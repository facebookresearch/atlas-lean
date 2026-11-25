# After an almost surely finite visit, later steps have the input law

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$ (self-loops $K(y, y) > 0$ are allowed).
Under the [law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md) $\mathbb{P}$ the steps
$\omega_n = (\xi_n, E_n)$, $n \in \mathbb{N}$, are i.i.d.: $\xi_n : \sigma \to \sigma$ has
independent coordinates $\xi_n(y) \sim K(y, \cdot)$, and $E_n$ is an independent exponential
clock of rate $1$. The [jump chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-chain.md) started at $x$ is
$Y_0 = x$, $Y_{n+1} = \xi_n(Y_n)$.

For states $x_0, x$ and $k \in \mathbb{N}$, let $\tau_k(\omega) \in \mathbb{N} \cup \{\infty\}$ be
the step of the [$k$-th visit](visit.md) (counting from $0$) to $x_0$ of the jump chain started
at $x$: the step $n$ with $Y_n = x_0$ and exactly $k$ earlier visits, and $\infty$ if there are
at most $k$ visits. If $\tau_k < \infty$ almost surely, then the
[steps from that visit on](shift-at.md), $(\omega_{\tau_k + n})_{n \in \mathbb{N}}$, again have
law $\mathbb{P}$: the image of $\mathbb{P}$ under $\omega \mapsto (\omega_{\tau_k(\omega) + n})_n$
is $\mathbb{P}$. On the null event $\{\tau_k = \infty\}$ the map leaves $\omega$ unshifted.
