# A common almost sure limit of time averages is the balanced-law mean

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$ (self-loops $K(y, y) > 0$ are allowed).
Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps $(\xi_k, E_k)$, $k \in \mathbb{N}$, are i.i.d.:
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$, and $E_k$ is
an independent exponential clock of rate $1$. Let $q : \sigma \to \mathbb{R}$ be positive rates
($q(y) > 0$ for every $y$) and $g : \sigma \to \mathbb{R}$ an observable with $0 \le g \le 1$.
Let $w$ be a probability law on $\sigma$ (weights $w(x) \ge 0$ with $\sum_x w(x) = 1$) that
balances the rate-weighted jump kernel,

$$\sum_{x \in \sigma} w(x)\, q(x)\, K(x, y) = w(y)\, q(y) \quad \text{for every } y \in \sigma,$$

with $\sum_x w(x)\, q(x) < \infty$. Assume that from every starting state $x$ the chain does not
explode, its [jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md) tending
to $\infty$ $\mathbb{P}$-almost surely, and that there is a real number $L$, the same for every
starting state, such that for every $x$, $\mathbb{P}$-almost surely,

$$\frac{1}{t} \int_0^t g(X^x_s)\, ds \to L \quad \text{as } t \to \infty,$$

where $X^x$ is the [path](../non-explosion-of-stochastic-reaction-networks/path.md) of the chain
started at $x$. Then

$$L = \sum_{x \in \sigma} w(x)\, g(x) .$$

The proof passes from time averages to Abel means with the
[Abelian theorem](tendsto-abel-of-tendsto-cesaro.md), takes expectations of the
[Abel functional](abel-sum.md) by bounded convergence, averages over $w$ by dominated
convergence, and evaluates the $w$-average with the
[resolvent identity](tsum-mul-lintegral-abel-sum.md).
