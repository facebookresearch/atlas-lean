# Inner mul Vec left of is Hermitian

A Hermitian matrix is its own adjoint: `inner ℂ (A x) y = inner ℂ x (A y)`. This combines
`inner_mulVec_left` with `Aᴴ = A` (`Matrix.IsHermitian.eq`).
