# Sorting the value blocks produces a shuffle

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. For `γ ∈ S_N`, put `α = blockRankLeft p q γ` and `β = blockRankRight p q
γ`. The permutation `γ * blockPermutation p q α⁻¹ β⁻¹` is increasing on each block and defines
`sortedBlockShuffle p q γ : Shuffle p q`.
