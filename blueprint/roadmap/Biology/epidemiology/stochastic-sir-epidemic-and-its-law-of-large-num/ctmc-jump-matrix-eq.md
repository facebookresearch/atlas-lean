# Jump matrix of a valid two-channel chain at an active state

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a set $\iota$: in state
$y$, channel $k \in \{1, 2\}$ has rate $\lambda_k(y) \ge 0$ and target $\theta_k(y)$, and
$\lambda_k(y) = 0$ when $\theta_k(y) = y$. Let $q = \lambda_1 + \lambda_2$ be its
[total rate](total-rate.md), $Q$ its [rate matrix](rate-matrix.md) and $\Pi$ the
[jump matrix](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-jump-matrix.md)
of $Q$. At an active state $x$, one with $q(x) \ne 0$ (so $q(x) > 0$), for every $z \in \iota$,

$$
\Pi(x, z) = \frac{\lambda_1(x)}{q(x)}\, [\theta_1(x) = z] +
\frac{\lambda_2(x)}{q(x)}\, [\theta_2(x) = z],
$$

where $[\theta_k(x) = z]$ is $1$ if $\theta_k(x) = z$ and $0$ otherwise. So the chain jumps to
$\theta_k(x)$ with probability $\lambda_k(x)/q(x)$, the two terms adding up when
$\theta_1(x) = \theta_2(x)$; at $z = x$ both sides are $0$.
