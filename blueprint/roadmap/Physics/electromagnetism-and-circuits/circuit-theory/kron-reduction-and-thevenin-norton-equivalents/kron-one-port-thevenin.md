# Kron reduction to one port gives a Thevenin equivalent

Let `p` be a finite set of interior nodes, `A` a real `1 × 1` matrix (the retained port), `B` a real
`1 × p` matrix and `D` a real `p × p` matrix, such that the conductance matrix `[[A, B], [Bᵀ, D]]`
is positive definite. Let `V`, `j_S` and `I` be real numbers, `φ_I` interior potentials and `j_I`
interior injections, with the full nodal equations

`A V + B φ_I = j_S − I` and `Bᵀ V + D φ_I = j_I`,

`j_S` the port source and `I` the load current out of the port. Then the
[port conductance](kron-port-conductance.md) `K = A − B D⁻¹ Bᵀ` is positive, the one-port law
`K V = j_eff − I` holds with the [effective injection](kron-port-injection.md)
`j_eff = j_S − B D⁻¹ j_I`, and so does the Thevenin form `V = j_eff / K − (1 / K) I`. The
reduction is the one-port case of the [Kron reduction theorem](kron-reduction-correct.md).
