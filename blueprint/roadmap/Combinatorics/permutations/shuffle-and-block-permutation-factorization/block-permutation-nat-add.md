# The right block keeps its permutation

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α ∈ S_p`, `β ∈ S_q`, and `j : Fin q`, `blockPermutation p q α β (R
j) = R(β j)`.
