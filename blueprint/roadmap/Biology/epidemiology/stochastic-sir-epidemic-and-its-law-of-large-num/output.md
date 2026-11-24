# Markov chain step read off one jump of the clock chain

Let $K$ be a [two-channel chain](two-channel.md) on a set $\iota$, with [total rate](total-rate.md)
$q(y)$ in state $y$. Take a state $x$, a [clock configuration](clock-config.md) $c$ with residual
clocks $r = (r_1, r_2)$, and an auxiliary step $(\eta, e)$, with $\eta : \iota \to \iota$ and
$e \in \mathbb{R}$. The output is the step $(\xi, E)$, a map $\xi : \iota \to \iota$ and a clock
$E \in \mathbb{R}$, of the
[jump-chain construction of a Markov chain path](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
given by

$$
\xi(y) = \begin{cases} \operatorname{next}(x, r) & \text{if } y = x, \\
\eta(y) & \text{if } y \ne x, \end{cases}
\qquad
E = \begin{cases} e & \text{if } q(x) = 0, \\ q(x)\, h(x, r) & \text{if } q(x) \ne 0, \end{cases}
$$

where $\operatorname{next}(x, r)$ is the [next state](next.md) and $h(x, r)$ the
[holding time](hold.md). So $\xi$ sends the current state to the next one and agrees with the
auxiliary map elsewhere, and the clock is the total rate times the holding time, or the auxiliary
clock when the total rate is $0$ (then $\operatorname{next}(x, r) = x$).
