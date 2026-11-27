# The sorted-block factorization

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, with `α = blockRankLeft p q γ` and `β = blockRankRight p
q γ`, `(sortedBlockShuffle p q γ).perm * blockPermutation p q α β = γ`.
