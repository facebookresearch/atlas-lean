# Rewards split at any step into earlier and restarted rewards

Let $S$ be a set, $q, g : S \to \mathbb{R}$, $x_0, x \in S$, $\omega$ a step sequence and
$n \in \mathbb{N}$, and suppose the jump chain started at $x$ is at $x_0$ at step $n$,
$Y_n(x, \omega) = x_0$. Then for every $i \in \mathbb{N}$ the [rewards](reward.md)
$R_m = \sum_{j < m} g(Y_j)\, E_j / q(Y_j)$ (with $a / 0 = 0$) satisfy

$$R_{n+i}(x, \omega) = R_n(x, \omega) + R_i(x_0, \theta_n \omega) ,$$

where $\theta_n \omega$, with $(\theta_n \omega)_m = \omega_{n+m}$, is the
[shifted step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md):
the last term is the reward of the chain restarted at $x_0$ with the shifted steps. Since $x_0$ is
only the state at step $n$, the identity holds at every step $n$, with $x_0 = Y_n(x, \omega)$.
