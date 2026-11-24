# Resolvent identity for weights balancing the rate-weighted jump kernel

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$ (self-loops $K(y, y) > 0$ are allowed).
Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps $(\xi_k, E_k)$, $k \in \mathbb{N}$, are i.i.d.:
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$, and $E_k$ is
an independent exponential clock of rate $1$. Let $q : \sigma \to \mathbb{R}$ be positive rates
($q(y) > 0$ for every $y$), and let $w : \sigma \to [0, \infty]$ be weights that balance the
rate-weighted jump kernel,

$$\sum_{x \in \sigma} w(x)\, q(x)\, K(x, y) = w(y)\, q(y) \quad \text{for every } y \in \sigma,$$

with $\sum_{x} w(x)\, q(x) < \infty$ (sums in $[0, \infty]$). The weights need not sum to $1$,
and their total may be infinite. Then for every $a > 0$ and every $g : \sigma \to \mathbb{R}$ with
$g \le 1$,

$$\sum_{x \in \sigma} w(x)\, \mathbb{E}_x[A_a g] = \sum_{x \in \sigma} w(x)\, g(x)^+ ,$$

an identity in $[0, \infty]$, where $g^+ = \max(g, 0)$ and
$\mathbb{E}_x[A_a g] = \int A_a g(x, \omega)\, d\mathbb{P}(\omega)$ is the expected
[Abel functional](abel-sum.md) of the chain started at $x$, a lower Lebesgue integral. Negative
values of $g$ count as $0$ on both sides.

Since the rates are positive and $\sum_x w(x)\, q(x) < \infty$, every $w(x)$ is finite and the
sums in the balance are finite. With the self-loops of $K$ included, the balance is then the
stationary master equation $w Q = 0$ of the generator
$Q(x, y) = q(x) \bigl(K(x, y) - \mathbf{1}_{x = y}\bigr)$. On the event where the clocks are
nonnegative and the jump times tend to $\infty$, the Abel functional of $g \ge 0$ is the
Laplace transform $a \int_0^\infty e^{-a t} g(X_t)\, dt$ of the path $X$ (the
[Laplace transform identity](lintegral-exp-path-eq-abel-sum.md)); this is why the identity is
read as the stationarity of $w$ in Laplace form. The proof multiplies the
[first-step equation](lintegral-abel-sum.md) by $(q(x) + a)\, w(x)$, sums over $x$, uses the
balance, and cancels the term $\sum_x w(x)\, q(x)\, \mathbb{E}_x[A_a g]$, which is finite because
for $g \le 1$ the Abel functional is [at most $1$](abel-sum-le-one.md) almost surely, before
dividing by $a > 0$.
