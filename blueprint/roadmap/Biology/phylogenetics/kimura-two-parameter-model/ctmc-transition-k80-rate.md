# K80 transition probabilities in closed form

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. For all real `κ` and `t`, the transition matrix `exp (t · R_κ)`, with
transition rate `α = κ/4` and transversion rate `β = 1/4`, is the [Kimura matrix](kimura-prob.md)
`T(κ t / 4, t / 4)`.
