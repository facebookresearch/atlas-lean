# Rates ≥ 0: monotone system failed by t iff its below-threshold set ∉ S

Let the scenario type $\Omega$ and the component type $E$ be finite, let $S \subseteq \{0, 1\}^E$ be
an
[increasing event](../../../Probability/correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md)
of configurations (a monotone system, not necessarily coherent), and let every rate be nonnegative,
$r(i, \omega) \ge 0$ for all components $i$ and scenarios $\omega$; initial damages $d_0(i, \omega)$
and thresholds $D(i, \omega)$ are arbitrary reals. Then for every time $t \ge 0$ and scenario
$\omega$, the scenario lies in the [system failure event](system-failure-event.md) at $t$, that is,
its system lifetime is at most $t$, if and only if

$$x(t) \notin S, \qquad x(t)_i = 1 \iff d_0(i, \omega) + r(i, \omega)\, t < D(i, \omega):$$

the system has failed by $t$ exactly when the configuration of the components whose damage is still
strictly below threshold at $t$ is not in $S$.
