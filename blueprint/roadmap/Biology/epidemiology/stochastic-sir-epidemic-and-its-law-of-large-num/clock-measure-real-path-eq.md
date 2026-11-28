# Transition probabilities of the clock chain

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a finite set $\iota$ with
the discrete σ-algebra (nonnegative rates, and rate $0$ for a channel whose jump would not move the
chain), $Q$ its [rate matrix](rate-matrix.md), which satisfies the
[conditions of a rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md),
$\mathbb{P}$ the [clock-configuration law](clock-measure.md) and $X_t(x, c)$ the
[path of the clock chain](path.md). For all $x, j \in \iota$ and $t \ge 0$ (Kolmogorov),

$$\mathbb{P}\bigl(X_t(x, \cdot) = j\bigr) = e^{tQ}(x, j),$$

where $e^{tQ}$ is the
[transition function](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)
of $Q$.
