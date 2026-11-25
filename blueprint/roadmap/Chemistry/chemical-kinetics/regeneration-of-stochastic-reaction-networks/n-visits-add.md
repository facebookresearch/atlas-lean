# Visit counts split at a visit into earlier and restarted counts

Let $S$ be a set, $x_0, x \in S$, $\omega$ a step sequence and $n \in \mathbb{N}$, and suppose the
jump chain started at $x$ is at $x_0$ at step $n$, $Y_n(x, \omega) = x_0$. Then for every
$i \in \mathbb{N}$ the [numbers of visits](n-visits.md) to $x_0$ satisfy

$$N_{n+i}(x_0, x, \omega) = N_n(x_0, x, \omega) + N_i(x_0, x_0, \theta_n \omega) ,$$

where $\theta_n \omega$, with $(\theta_n \omega)_m = \omega_{n+m}$, is the
[shifted step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md):
the last term counts the visits to $x_0$ before step $i$ of the chain restarted at $x_0$ with the
shifted steps.
