# Inclusion of the left permutation group

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. `blockLeftHom p q : S_p →* S_N` sends `α` to `blockPermutation p q α 1`,
acting on the left block and fixing the right block.
