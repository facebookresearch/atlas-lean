# Finite matrix star equivalence of the Calkin algebra

Let `H` be a complete complex
Hilbert space with Hilbert basis `b : HilbertBasis ι ℂ H`, an index bijection `e : Fin 2 ×
ι ≃ ι`, and `N : ℕ+`. Let `U_i b_j=b_(e(i,j))`, and obtain `S_N` from `[I]` by splitting
each last leaf `V` into `V U_0,V U_1`. Write `q : B(H) → Q(H)` for the Calkin quotient and
`c_i=q(S_N(i))`. `finiteMatrixFold b e N : M_N(Q(H)) ≃⋆ₐ[ℂ] Q(H)` sends `X` to `Σ_i,j c_i
X_ij c_j*`, with inverse entries `c_i* z c_j`.
