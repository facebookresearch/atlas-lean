# One jump of the clocks from an active state

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a finite set $\iota$ with
the discrete σ-algebra: in state $y$, channel $k \in \{1, 2\}$ has rate $\lambda_k(y) \ge 0$ and
target $\theta_k(y)$, and $\lambda_k(y) = 0$ when $\theta_k(y) = y$. Let $x$ be an active state, one
with [total rate](total-rate.md) $q(x) = \lambda_1(x) + \lambda_2(x) \ne 0$. Suppose the
[clock configuration](clock-config.md) $c$, with residual clocks $r$, has the
[clock-configuration law](clock-measure.md) $\mathbb{P}$: the residual clocks and all the future interarrival
times are independent and exponential with rate $1$. Then the [next state](next.md)
$\operatorname{next}(x, r)$, the total clock $q(x)\, h(x, r)$, where $h$ is the
[holding time](hold.md), and the [clock configuration after the jump](next-clock.md) $c'$ are
independent, and

- $\operatorname{next}(x, r)$ has law $\Pi(x, \cdot)$, the
  [row at $x$ of the jump matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-pmf.md)
  of the [rate matrix](rate-matrix.md) of $K$, with
  $\Pi(x, z) = (\lambda_1(x) [\theta_1(x) = z] + \lambda_2(x) [\theta_2(x) = z]) / q(x)$
  ([jump matrix at an active state](ctmc-jump-matrix-eq.md));
- $q(x)\, h(x, r)$ has the rate-$1$ exponential law $\operatorname{Exp}(1)$;
- $c'$ has the clock-configuration law $\mathbb{P}$ again.

In other words, the image of $\mathbb{P}$ under
$c \mapsto \bigl((\operatorname{next}(x, r), q(x)\, h(x, r)), c'\bigr)$ is the product
$\Pi(x, \cdot) \otimes \operatorname{Exp}(1) \otimes \mathbb{P}$. The proof combines
[competing exponential clocks](lintegral-competing.md) with the memoryless property of the
exponential law.
