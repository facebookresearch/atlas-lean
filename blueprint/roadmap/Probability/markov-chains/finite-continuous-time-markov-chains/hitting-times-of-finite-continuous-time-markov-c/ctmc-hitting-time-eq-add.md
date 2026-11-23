# First-jump decomposition of a hitting time

Let $Q$ be a real square matrix indexed by a set $S$, $A \subseteq S$, and $i \notin A$. For every
step sequence $\omega = ((\xi_n, E_n))_{n \in \mathbb{N}}$, the [hitting time](ctmc-hitting-time.md)
of $A$ by the [path](../finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) started at
$i$ is the first [holding time](../finite-continuous-time-markov-chains-as-path-pro/ctmc-holding-time.md)
plus the hitting time of the path started at the first jump target $\xi_0(i)$ and driven by the
[shifted steps](../finite-continuous-time-markov-chains-as-path-pro/ctmc-shift.md)
$\theta_1 \omega = (\omega_{n+1})_n$:

$$H_A(i, \omega) = S_0(i, \omega) + H_A(\xi_0(i), \theta_1 \omega)$$

in $[0, \infty]$.
