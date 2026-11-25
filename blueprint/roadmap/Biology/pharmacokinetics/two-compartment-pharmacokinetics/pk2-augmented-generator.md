# Two-compartment generator augmented with an elimination sink

For rates `k10` (elimination from the central compartment), `k12` (transfer from the central to the
peripheral compartment) and `k21` (transfer back), all real, the augmented generator is the 3 × 3
matrix `[[-(k10 + k12), k21, 0], [k12, -k21, 0], [k10, 0, 0]]`, acting on the state
`(A₁, A₂, sink)`: the eliminated amount enters the sink, a third state, at the rate `k10 * A₁`.
