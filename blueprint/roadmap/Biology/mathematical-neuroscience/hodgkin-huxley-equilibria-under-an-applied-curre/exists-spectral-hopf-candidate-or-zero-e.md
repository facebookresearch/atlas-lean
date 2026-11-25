# A spectral Hopf candidate or a zero eigenvalue below 15 mV

There is a voltage `V*` with `0 < V* < 15` mV such that the [branch point](eq-point.md)
`x* = (V*, m∞(V*), h∞(V*), n∞(V*))` is an equilibrium of the
[squid system with applied current](squid-i.md) `I* = I∞(V*)`, the
[squid steady-state current](iss.md) at `V*`, and either

- the [Jacobian](../hodgkin-huxley-model/jac.md) of the squid field at `x*` is the
  [arrowhead matrix](mat.md) of the [entries at V*](arrow-at.md) and satisfies the
  [spectral Hopf conditions](is-spectral-hopf-candidate.md) for some `ω` (`ω > 0`, `± i ω` are
  eigenvalues, `i ω` is a simple root of the characteristic quartic and every other eigenvalue has
  negative real part), and for every `W` with `0 ≤ W < V*` the Jacobian at the branch point over
  `W`, an equilibrium for the current `I∞(W)`, is
  [Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md).
  So `V*` is the first voltage in `[0, 15]` at which the Jacobian along the branch stops being
  Hurwitz; or
- `0` is an eigenvalue of the Jacobian at `x*`, [equivalently](zero-mem-spectrum-jac-iff.md)
  `I∞'(V*) = 0`. This alternative says nothing about the branch below `V*`.

The statement asserts neither transversality nor the nondegeneracy conditions of a fold. A voltage
`V*` satisfying the first alternative [always exists](exists-spectral-hopf-candidate.md).
