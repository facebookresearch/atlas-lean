# Two-compartment generator

For rates `k10` (elimination from the central compartment), `k12` (transfer from the central to the
peripheral compartment) and `k21` (transfer back), all real, the two-compartment generator is the 2
× 2 matrix `M = [[-(k10 + k12), k21], [k12, -k21]]`, the matrix of the linear amount dynamics
`A' = M A` for the amounts `A = (A1, A2)`. In the model the rates are nonnegative.
