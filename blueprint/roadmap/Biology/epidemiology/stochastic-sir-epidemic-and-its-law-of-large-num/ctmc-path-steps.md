# The path does not depend on the auxiliary steps

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$ with [rate matrix](rate-matrix.md)
$Q$, $x \in \iota$ and $c$ a [clock configuration](clock-config.md). For every sequence $f$ of
auxiliary steps and every $t \ge 0$, the
[Markov chain path](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
$X^Q_t$ with matrix $Q$ started at $x$ and driven by the
[steps read off the clock chain](steps.md) $\omega(x, c, f)$ is the
[path of the clock chain](path.md) $X_t(x, c)$:

$$X^Q_t\bigl(x, \omega(x, c, f)\bigr) = X_t(x, c).$$

The auxiliary steps enter the read-off steps only away from the current state and at states of
[total rate](total-rate.md) $0$, which changes neither the jump chain nor the jump times.
