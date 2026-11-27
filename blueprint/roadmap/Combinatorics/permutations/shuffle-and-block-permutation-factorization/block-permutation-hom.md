# The two-block permutation homomorphism

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. The assignment `(α,β) ↦ blockPermutation p q α β` is the monoid
homomorphism `S_p × S_q →* S_N`.
