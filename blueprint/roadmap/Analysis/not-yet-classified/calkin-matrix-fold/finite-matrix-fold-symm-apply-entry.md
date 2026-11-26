# Inverse entry of the finite Calkin fold

Let `H` be a complete complex Hilbert space
with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 × ι ≃ ι`, and
`N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting each last
leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. for `z ∈ Q(H)` and `i,j ∈ Fin N`, `(finiteMatrixFold b e N).symm z i
j=c_i* z c_j`.
