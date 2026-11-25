# Conditional failure probability given a bin, for nonnegative weights

Let the scenario type $\Omega$ and the component type $E$ be finite. Take scenario weights
$p(\omega) \ge 0$, which need not sum to one; an
[increasing](../../../Probability/correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md)
system event $S \subseteq \{0, 1\}^E$; initial damages $d_0(i, \omega)$, nonnegative rates
$r(i, \omega) \ge 0$ and thresholds $D(i, \omega)$; a sensor with gain $g \ne 0$ and offset $b$ on
component $i_0$, with errors $\varepsilon(\omega)$; a time $t \ge 0$ and bin bounds
$z_{\mathrm{lo}}$, $z_{\mathrm{hi}}$. Let $A$ be the [bin event](bin-event.md) of the reading
$z(\omega) = g\, (d_0(i_0, \omega) + r(i_0, \omega)\, t) + b + \varepsilon(\omega)$, let $F$ be the
[system failure event](system-failure-event.md) at $t$, write
$P(B) = \sum_{\omega \in B} p(\omega)$, and assume $P(A) > 0$. The weights normalized on $A$,
$p_A(\omega) = p(\omega) / P(A)$ for $\omega \in A$ and $p_A(\omega) = 0$ otherwise, satisfy:

- $p_A(\omega) \ge 0$ for every $\omega$ and $\sum_{\omega} p_A(\omega) = 1$: they are a probability
  distribution on $\Omega$;
- $\sum_{\omega \in F} p_A(\omega) = P(A \cap F) / P(A)$, and this number lies in $[0, 1]$;
- $\omega \in A \cap F$ exactly when $z_{\mathrm{lo}} \le z(\omega) \le z_{\mathrm{hi}}$ and the
  configuration $x(t)$, with $x(t)_i = 1$ exactly when
  $d_0(i, \omega) + r(i, \omega)\, t < D(i, \omega)$, is not in $S$.

So $P(A \cap F) / P(A)$ is the probability that the system has failed by $t$, conditional on the
reading lying in the bin, under the scenario law proportional to $p$. The hypothesis $P(A) > 0$,
which holds exactly when some scenario of the bin has positive weight, is part of the definition of
$p_A$: a bin of zero weight has no normalized weights, and no conditional value is assigned to it.
No independence between components, sensor errors and damage is assumed, since the scenario weights
are joint. One time $t$ and one bin are treated.
