# Integrals against a row of the jump matrix at an active state

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a finite set $\iota$ with
the discrete σ-algebra: in state $y$, channel $k \in \{1, 2\}$ has rate $\lambda_k(y) \ge 0$ and
target $\theta_k(y)$, and $\lambda_k(y) = 0$ when $\theta_k(y) = y$. Its
[rate matrix](rate-matrix.md) $Q$ then satisfies the
[conditions of a rate matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/rate-matrices-of-finite-continuous-time-markov-c/is-rate-matrix.md).
Let $x$ be an active state, one with [total rate](total-rate.md)
$q(x) = \lambda_1(x) + \lambda_2(x) \ne 0$, and $\Pi(x, \cdot)$ the probability measure on $\iota$
given by the
[row at $x$ of the jump matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-pmf.md)
of $Q$. For every function $\psi : \iota \to [0, \infty]$,

$$
\int \psi \, d\Pi(x, \cdot) = \frac{\lambda_1(x)}{q(x)}\, \psi(\theta_1(x)) +
\frac{\lambda_2(x)}{q(x)}\, \psi(\theta_2(x)),
$$

a lower Lebesgue integral with values in $[0, \infty]$, here a finite weighted sum (with
$0 \cdot \infty = 0$).
