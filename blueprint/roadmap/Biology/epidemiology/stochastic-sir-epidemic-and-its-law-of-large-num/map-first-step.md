# Independent Exp(1) clocks and step-law auxiliary steps give a first step with the step law

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a finite set $\iota$ with
the discrete σ-algebra (nonnegative rates, and rate $0$ for a channel whose jump would not move the
chain), and $Q$ its [rate matrix](rate-matrix.md), which satisfies the
[conditions of a rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md).
Let $\mu_Q$ be the
[law of one step](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-step-measure.md)
of the Markov chain construction and $\mathbb{P}_Q = \mu_Q^{\otimes \mathbb{N}}$ the
[law of the step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md).
Let the input $(c, g)$ have law $\mathbb{P} \otimes \mathbb{P}_Q$: the
[clock configuration](clock-config.md) $c$ has the [clock-configuration law](clock-measure.md) $\mathbb{P}$
(independent rate-$1$ exponential residual clocks and interarrival times), the auxiliary steps
$g_0, g_1, \dots$ are i.i.d. with law $\mu_Q$, and $c$ and $g$ are independent. Then, for every
starting state $x \in \iota$, the [first step and the restarted input](first-step.md) are
independent, the first step has law $\mu_Q$, and the restarted input has the law
$\mathbb{P} \otimes \mathbb{P}_Q$ of the input again: the image of $\mathbb{P} \otimes \mathbb{P}_Q$
under the map to the first step and the restarted input is
$\mu_Q \otimes (\mathbb{P} \otimes \mathbb{P}_Q)$.
