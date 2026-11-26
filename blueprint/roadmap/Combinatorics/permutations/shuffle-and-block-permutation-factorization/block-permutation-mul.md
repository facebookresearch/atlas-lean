# Block permutations respect multiplication

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `α,α' ∈ S_p` and `β,β' ∈ S_q`, `blockPermutation(α*α',β*β') =
blockPermutation(α,β) * blockPermutation(α',β')`.
