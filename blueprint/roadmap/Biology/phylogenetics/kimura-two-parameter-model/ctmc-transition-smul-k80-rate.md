# Closed-form exponential of a rate-scaled K80 matrix

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. For all real `c`, `κ` and `t`, the scaled matrix `c · R_κ`, with
transition rate `α = c κ / 4` and transversion rate `β = c / 4`, has matrix exponential
`exp (t · c · R_κ) = T(c κ t / 4, c t / 4)`, the [Kimura matrix](kimura-prob.md) at `a = α t` and
`b = β t`. It is a transition probability matrix, of a K80 chain with nonnegative rates, when for
example `c ≥ 0`, `κ ≥ 0` and `t ≥ 0`.
