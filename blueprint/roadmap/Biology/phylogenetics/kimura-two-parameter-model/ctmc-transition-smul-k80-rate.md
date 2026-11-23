# Closed-form transition matrix of a rate-scaled K80 model

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. For all real `c`, `κ` and `t`, the rate-scaled model `c · R_κ`, with
transition rate `α = c κ / 4` and transversion rate `β = c / 4`, has transition matrix
`exp (t · c · R_κ) = T(c κ t / 4, c t / 4)`, the [Kimura matrix](kimura-prob.md) at `a = α t` and
`b = β t`.
