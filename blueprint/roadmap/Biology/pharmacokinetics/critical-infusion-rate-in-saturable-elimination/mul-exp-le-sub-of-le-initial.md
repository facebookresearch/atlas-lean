# The gap closes no faster than exponentially, from above

Let `Vmax > 0` and `Km > 0`, let `R` be a real infusion rate, and let `C` be differentiable at every
time `t ≥ 0` with `C'(t) = R - Vmax * C(t) / (Km + C(t))` (saturable elimination under constant
infusion). Let `c ≥ 0` be an equilibrium: `Vmax * c / (Km + c) = R`.

If `c ≤ C(0)`, then `(C(0) - c) * exp (-λ t) ≤ C(t) - c` for every `t ≥ 0`, with
`λ = (Vmax - R) / (Km + c)`.
