# Ranks in the right value block

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, `blockRankRight p q γ = (Tuple.sort (fun j : Fin q ↦ γ(R
j)))⁻¹ ∈ S_q`. It records the rank of each right-block value in its ascending order.
