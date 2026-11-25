# Between 0 and 15 mV, Δ₃ first vanishes or the Jacobian is singular

Let `p₃(V)`, `p₄(V)` and `Δ₃(V)` be the [linear](coef-3.md) and [constant](coef-4.md) coefficients
and the [third Hurwitz determinant](hdet.md) of the characteristic quartic of the
[arrowhead entries at V](arrow-at.md), the entries of the squid Jacobian at the branch point over
`V`. There is a voltage `V*` with `0 < V* < 15` mV such that either

- `Δ₃(V*) = 0`, `p₃(V*) > 0` and `p₄(V*) > 0`, and `p₃(W) > 0`, `p₄(W) > 0` and `Δ₃(W) > 0` for
  every `W` with `0 ≤ W < V*`. With `p₁ > 0`, which holds at every voltage, these are the
  [Routh–Hurwitz conditions](is-hurwitz-of-hdet-pos.md), so `V*` is the first voltage from rest at
  which they fail; or
- `p₄(V*) = 0`, that is, `0` is an [eigenvalue](zero-mem-spectrum-iff.md) of the Jacobian at the
  branch point over `V*`. This alternative says nothing about the voltages below `V*`, where the
  Routh–Hurwitz conditions may already fail.

The voltage `V = 0` is the resting state, the branch point for the applied current `I = 0`.
