# The K80 exponential at ratio one is the Jukes–Cantor matrix

For every real `t`, the
[K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md) `R_1` with
transition/transversion ratio `κ = 1`, rate `1/4` to each other base, has matrix exponential
`exp (t · R_1)` equal to the [Jukes–Cantor matrix](../jukes-cantor-model/jc-prob.md) with
substitution rate `μ = 3/4`, whose entries are `1/4 + 3/4 · e^(-t)` on the diagonal and
`1/4 - 1/4 · e^(-t)` off it. For `t ≥ 0` it is a transition probability matrix.
