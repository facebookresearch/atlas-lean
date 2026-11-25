# Diagonalization of the scaled K80 rate matrix

Write `R_κ` for the [K80 rate matrix](../time-reversible-nucleotide-substitution-models/k80-rate.md)
with transition/transversion ratio `κ`: `-(κ + 2)/4` on the diagonal, `κ/4` for a transition and
`1/4` for a transversion. For all real `κ` and `t`,
`t · R_κ = V · diag (0, -t, -(κ + 1) t / 2, -(κ + 1) t / 2) · V⁻¹`, where `V` is the
[K80 eigenbasis](k80-eigenbasis.md) and `V⁻¹` its [inverse](k80-eigenbasis-unit.md).
