# System failure event of linear damage paths at time t

Let the scenario type $\Omega$ and the component type $E$ be finite. For each component $i$ and
scenario $\omega$ let $d_0(i, \omega)$, $r(i, \omega)$ and $D(i, \omega)$ be an initial damage, a
rate and a threshold, all real, and let $\tau_i(\omega)$ be the
[lifetime](../fracture-fatigue-crack-growth-and-failure-margin/damage-lifetime.md) of the
[linear damage path](linear-damage.md) $d_0(i, \omega) + r(i, \omega)\, s$ against $D(i, \omega)$.
Let $S$ be a set of
[configurations](../../../Probability/random-fields/spin-and-bond-configuration-spaces/config-space.md)
$x \in \{0, 1\}^E$, where $x_i = 1$ means that component $i$ is up. The system lifetime in scenario
$\omega$ is

$$T(\omega) = \max_{x \in S} \min_{i : x_i = 1} \tau_i(\omega) \in [0, \infty],$$

a minimum over no component being $\infty$ and a maximum over no configuration $0$. The system
failure event at time $t \ge 0$ is the set of scenarios $\{\omega \in \Omega : T(\omega) \le t\}$.
If $S$ contains the configuration with every component down (for example the set of all
configurations), $T(\omega) = \infty$ and the event is empty.

The definition takes any set $S$ and rates of any sign: for $S$ empty the system lifetime is $0$ and
every scenario is in the event. In the physical reading the rates are nonnegative, so that damage
accumulates. Reading $S$ as the up configurations of a monotone system needs $S$ to be an
[increasing event](../../../Probability/correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md),
as in the [membership criterion](mem-system-failure-event-iff.md).
