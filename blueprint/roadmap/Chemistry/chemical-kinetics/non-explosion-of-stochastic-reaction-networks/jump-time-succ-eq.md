# First-step decomposition of the jump times

Let $S$ be a set, $q : S \to \mathbb{R}$, $x \in S$ and $\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$
a step sequence, with [jump times](jump-time.md) $T_j(x, \omega)$. For every $j \in \mathbb{N}$,

$$T_{j+1}(x, \omega) = \frac{E_0}{q(x)} + T_j\bigl(\xi_0(x), \theta_1 \omega\bigr),$$

where $\theta_1 \omega = (\omega_1, \omega_2, \dots)$ is the
[shift](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md)
of $\omega$ by one step: the first holding time plus the jump times of the shifted steps started at
the first jump $\xi_0(x)$. The identity holds for every real $q$, with the convention $a / 0 = 0$ of
the holding times, so that $E_0 / q(x) = 0$ when $q(x) = 0$.
