# Finite-dimensional distributions of the clock chain

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a finite set $\iota$ with
the discrete σ-algebra (nonnegative rates, and rate $0$ for a channel whose jump would not move the
chain), $Q$ its [rate matrix](rate-matrix.md), which satisfies the
[conditions of a rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md),
$x \in \iota$, $\mathbb{P}$ the [clock-configuration law](clock-measure.md) and $X_t(x, c)$ the
[path of the clock chain](path.md). Let $s_0, \dots, s_{n-1} \ge 0$ be increments,
$t_k = s_0 + \dots + s_k$, and $j_0, \dots, j_{n-1} \in \iota$. Then, with $j_{-1} = x$,

$$
\mathbb{P}\bigl(X_{t_k}(x, \cdot) = j_k \text{ for } k = 0, \dots, n - 1\bigr)
= \prod_{k=0}^{n-1} e^{s_k Q}(j_{k-1}, j_k),
$$

where $e^{sQ}$ is the
[transition function](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)
of $Q$. For $n = 0$ both sides are $1$.
