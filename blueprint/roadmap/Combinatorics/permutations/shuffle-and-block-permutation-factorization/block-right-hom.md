# Inclusion of the right permutation group

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. `blockRightHom p q : S_q →* S_N` sends `β` to `blockPermutation p q 1
β`, fixing the left block and acting on the right block.
