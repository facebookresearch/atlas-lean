# Ranks in the left value block

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, `blockRankLeft p q γ = (Tuple.sort (fun i : Fin p ↦ γ(L
i)))⁻¹ ∈ S_p`. It records the rank of each left-block value in its ascending order.
