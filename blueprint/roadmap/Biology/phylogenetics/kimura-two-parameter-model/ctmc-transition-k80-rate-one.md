# K80 with ratio one has the Jukes–Cantor transition matrix

For every real `t`, the
[K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md) `R_1` with
transition/transversion ratio `κ = 1`, rate `1/4` to each other base, has transition matrix
`exp (t · R_1)` equal to the [Jukes–Cantor transition probability](../jukes-cantor-model/jc-prob.md)
matrix with substitution rate `μ = 3/4`, whose entries are `1/4 + 3/4 · e^(-t)` on the diagonal and
`1/4 - 1/4 · e^(-t)` off it.
