# Port conductance of a one-port Kron reduction

Let `p` be a finite set of interior nodes, `A` a real `1 × 1` matrix (the retained port), `B` a real
`1 × p` matrix and `D` a real `p × p` matrix, the blocks of the conductance matrix
`[[A, B], [Bᵀ, D]]`. The port conductance of the one-port Kron reduction is the single entry of the
Schur complement

`K = A − B D⁻¹ Bᵀ`.

The intended domain is `D` invertible, for example when the whole conductance matrix is positive
definite; with the convention that the inverse of a singular matrix is `0`, `K` is the entry of
`A` when `D` is singular.
