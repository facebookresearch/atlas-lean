# If I∞' > 0 on 0 ≤ V ≤ 15 mV, the branch has a spectral Hopf candidate

Suppose the derivative of the [squid steady-state current](iss.md) is positive on the closed
interval: `I∞'(V) > 0` for every `V` with `0 ≤ V ≤ 15` mV (so `I∞` is strictly increasing there).
Then there is a voltage `V*` with `0 < V* < 15` mV such that

- the applied current `I* = I∞(V*)` satisfies `0 < I* < I∞(15)`;
- the [branch point](eq-point.md) `(V*, m∞(V*), h∞(V*), n∞(V*))` is an equilibrium of the
  [squid system with applied current I*](squid-i.md);
- the [arrowhead matrix](mat.md) of the [entries at V*](arrow-at.md), which is the squid Jacobian at
  that point, satisfies the [spectral Hopf conditions](is-spectral-hopf-candidate.md) for some `ω`;
- for every `W` with `0 ≤ W < V*`, the Jacobian at the branch point over `W`, an equilibrium for the
  current `I∞(W)`, is
  [Hurwitz](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-hurwitz.md).

The hypothesis rules out the [zero-eigenvalue alternative](exists-spectral-hopf-candidate-or-zero-e.md)
at `V*`.
