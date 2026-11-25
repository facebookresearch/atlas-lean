# Over a window a ≤ b, metabolic energy is at least mechanical work

Let `a ≤ b` be real times, let the efficiency `η` satisfy `0 < η ≤ 1`, and let `P_base` and
`P_mech` be real functions of time with `P_base(t) ≥ 0` and `P_mech(t) ≥ 0` at every time `t`, both
integrable on `[a, b]`. Then the mechanical work over the window is at most the metabolic energy of
the declared power model `P_met = P_base + P_mech / η`:

`∫ₐᵇ P_mech(t) dt ≤ ∫ₐᵇ (P_base(t) + P_mech(t) / η) dt`.

The order `a ≤ b` matters: the integrals are oriented, so for `a > b` the inequality is reversed.
