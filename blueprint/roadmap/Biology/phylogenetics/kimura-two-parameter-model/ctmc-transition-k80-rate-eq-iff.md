# Identifiability under the K80 normalization

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. For all real `κ₁`, `t₁`, `κ₂` and `t₂`,
`exp (t₁ · R_κ₁) = exp (t₂ · R_κ₂)` if and only if `t₁ = t₂` and `κ₁ t₁ = κ₂ t₂`. With the
transversion rate fixed at `β = 1/4`, the transition matrix determines `t` and `κ t`, hence `κ` when
`t ≠ 0`.
