# The block inclusions give the combined permutation

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α ∈ S_p` and `β ∈ S_q`, `blockLeftHom p q α * blockRightHom p q β =
blockPermutation p q α β`.
