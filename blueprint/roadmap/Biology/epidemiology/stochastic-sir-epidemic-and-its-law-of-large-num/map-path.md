# Under independent rate-one exponential clocks the path has the law of the Markov chain

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a finite set $\iota$ with
the discrete σ-algebra (nonnegative rates, and rate $0$ for a channel whose jump would not move the
chain), $Q$ its [rate matrix](rate-matrix.md), which satisfies the
[conditions of a rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md),
and $x \in \iota$. Let the [clock configuration](clock-config.md) $c$ have the
[clock-configuration law](clock-measure.md) $\mathbb{P}$: the residual clocks and the interarrival times are
independent and exponential with rate $1$. Then the [path of the clock chain](path.md)
$(X_t(x, c))_{t \ge 0}$ has the same law as the path $(X^Q_t(x, \omega))_{t \ge 0}$ of the
continuous-time Markov chain with rate matrix $Q$
[built from its jump chain and holding times](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md),
with $\omega$ distributed according to the
[law of the step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md)
$\mathbb{P}_Q$:

$$
\mathbb{P} \circ \bigl(c \mapsto (X_t(x, c))_{t \ge 0}\bigr)^{-1}
= \mathbb{P}_Q \circ \bigl(\omega \mapsto (X^Q_t(x, \omega))_{t \ge 0}\bigr)^{-1}.
$$

Both laws are measures on the space of all functions $[0, \infty) \to \iota$ with the product
σ-algebra.
