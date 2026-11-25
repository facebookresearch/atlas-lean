# Squid branch first stops being Hurwitz at a spectral Hopf candidate

There is a voltage `V*` with `0 < V* < 15` mV such that

- the applied current `I* = I∞(V*)`, with `I∞` the [squid steady-state current](iss.md), satisfies
  `0 < I* < I∞(15)`;
- the [branch point](eq-point.md) `(V*, m∞(V*), h∞(V*), n∞(V*))` is an equilibrium of the
  [squid system with applied current I*](squid-i.md);
- the [arrowhead matrix](mat.md) of the [entries at V*](arrow-at.md), which is the squid Jacobian at
  that point, satisfies the [spectral Hopf conditions](is-spectral-hopf-candidate.md) for some `ω`:
  `ω > 0`, `± i ω` are eigenvalues, `i ω` is a simple root of the characteristic quartic and every
  other eigenvalue has negative real part; in particular `0` is not an eigenvalue;
- for every `W` with `0 ≤ W < V*`, the Jacobian at the branch point over `W`, an equilibrium for the
  current `I∞(W)`, is
  [Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md).

So, going up the branch from rest, `V*` is the first voltage at which the Jacobian stops being
Hurwitz. This is the [conditional form](exists-spectral-hopf-candidate-of-deriv.md) with its
hypothesis met: the squid steady-state current has a
[positive derivative](../hodgkin-huxley-model/steady-current-deriv-squid-pos.md) on `[-12, 115]` mV.
The statement does not include transversality, so `V*` is a Hopf candidate, not a Hopf bifurcation.
