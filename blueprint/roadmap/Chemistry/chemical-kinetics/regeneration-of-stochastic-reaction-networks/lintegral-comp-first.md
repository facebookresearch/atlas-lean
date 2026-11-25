# First-step analysis: averaging over the first jump target

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons (so every
subset of $\sigma$ is measurable), and let $K$ be a jump kernel on $\sigma$: a probability mass
function $K(y, \cdot)$ on $\sigma$ for each state $y$. Under the
[law of the step sequence](../non-explosion-of-stochastic-reaction-networks/input-measure.md)
$\mathbb{P}$, a probability measure, the steps of $\omega = ((\xi_k, E_k))_{k \ge 0}$ are i.i.d.:
$\xi_k : \sigma \to \sigma$ has independent coordinates $\xi_k(y) \sim K(y, \cdot)$, and $E_k$ is
an independent exponential clock of rate $1$. Let $x \in \sigma$, and let $F$ assign to each state
$y$ and each step sequence $\omega$ a value $F(y, \omega) \in [0, \infty]$, measurable in $\omega$
for every $y$. Then

$$
\int F(\xi_0(x), \theta_1 \omega)\, d\mathbb{P}(\omega) = \sum_{y \in \sigma} K(x, y)
\int F(y, \omega)\, d\mathbb{P}(\omega),
$$

with lower Lebesgue integrals and sums in $[0, \infty]$ (with $0 \cdot \infty = 0$), where
$\theta_1 \omega = ((\xi_{k+1}, E_{k+1}))_{k \ge 0}$ is the
[shifted step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md).
The first jump target $\xi_0(x)$ of the chain started at $x$ has law $K(x, \cdot)$ and is
independent of the later steps $\theta_1 \omega$, which have the law $\mathbb{P}$ again; the first
clock $E_0$ does not enter.
