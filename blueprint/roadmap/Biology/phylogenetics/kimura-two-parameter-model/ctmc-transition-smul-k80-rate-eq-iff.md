# Only the composite parameters are identifiable

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. For all real `c₁`, `κ₁`, `t₁`, `c₂`, `κ₂` and `t₂`, the rate-scaled K80
models give the same transition matrix, `exp (t₁ · c₁ · R_κ₁) = exp (t₂ · c₂ · R_κ₂)`, if and only
if `c₁ t₁ = c₂ t₂` and `c₁ κ₁ t₁ = c₂ κ₂ t₂`, that is, they have the same `β t = c t / 4` and
`α t = c κ t / 4`. In particular the rate scale `c` and the time `t` enter only through their
product.
