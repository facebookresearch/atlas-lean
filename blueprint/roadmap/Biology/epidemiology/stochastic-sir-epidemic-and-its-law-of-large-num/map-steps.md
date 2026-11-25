# Independent Exp(1) clocks and i.i.d. step-law auxiliary steps give i.i.d. step-law read-off steps

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a finite set $\iota$ with
the discrete σ-algebra (nonnegative rates, and rate $0$ for a channel whose jump would not move the
chain), $Q$ its [rate matrix](rate-matrix.md), which satisfies the
[conditions of a rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md),
$\mu_Q$ the
[law of one step](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-step-measure.md)
of the Markov chain construction and $\mathbb{P}_Q = \mu_Q^{\otimes \mathbb{N}}$ the
[law of the step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md).
Let the [clock configuration](clock-config.md) $c$ have the [clock-configuration law](clock-measure.md)
$\mathbb{P}$ (independent rate-$1$ exponential residual clocks and interarrival times) and let the
auxiliary steps $g = (g_n)_{n \in \mathbb{N}}$ be i.i.d. with law $\mu_Q$ and independent of $c$, so
that $(c, g)$ has law $\mathbb{P} \otimes \mathbb{P}_Q$. Then, for every $x \in \iota$, the
[steps read off the clock chain](steps.md) $\omega(x, c, g)$ started at $x$ are i.i.d. with law
$\mu_Q$: the image of $\mathbb{P} \otimes \mathbb{P}_Q$ under $(c, g) \mapsto \omega(x, c, g)$ is
$\mathbb{P}_Q$. This follows from the [first-step statement](map-first-step.md) by induction.
