# Joint law of the first step and the shifted step sequence

Let $S$ be a set with a σ-algebra, $P$ a jump kernel on $S$ (a probability mass function
$P(x, \cdot)$ on $S$ for each $x \in S$), $\mu_P$ the [law of one step](step-measure.md) and
$\mathbb{P}_P = \bigotimes_{n \in \mathbb{N}} \mu_P$ the [input law](input-measure.md) on step
sequences $\omega = (\omega_0, \omega_1, \dots)$. The map
$\omega \mapsto (\omega_0, \theta_1 \omega)$, where $\theta_1 \omega = (\omega_1, \omega_2, \dots)$
is the [shift](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md)
by one step, pushes $\mathbb{P}_P$ forward to the product measure $\mu_P \otimes \mathbb{P}_P$.

So under the input law the first step and the shifted sequence are independent, the first step has
the step law $\mu_P$, and the shifted sequence has the input law again. This is the special case
$\mu = \mu_P$ of the [head–tail decomposition of an i.i.d. sequence with marginal $\mu$](../../../Biology/epidemiology/stochastic-sir-epidemic-and-its-law-of-large-num/infinite-pi-map-head-tail.md).
