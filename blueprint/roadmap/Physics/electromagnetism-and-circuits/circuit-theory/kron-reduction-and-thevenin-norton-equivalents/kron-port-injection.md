# Effective injected current of a one-port Kron reduction

Let `p` be a finite set of interior nodes, `B` a real `1 × p` matrix, `D` a real `p × p` matrix,
`j_S` a real port source current and `j_I ∈ ℝᵖ` interior injections. The effective injected current
of the one-port Kron reduction is the port source corrected by the interior injections,

`j_eff = j_S − B D⁻¹ j_I`.

The intended domain is `D` invertible; with the convention that the inverse of a singular matrix
is `0`, `j_eff = j_S` when `D` is singular.
