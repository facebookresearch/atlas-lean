# Uniqueness of shuffle and block factors

Let `p,q : ℕ`, `N = p+q`, and `S_r = Equiv.Perm (Fin r)`. Write `L(i) = Fin.castAdd q i` and
`R(j) = Fin.natAdd p j` for the two ordered blocks of `Fin N`; permutation multiplication is
`(u*v)(i) = u(v(i))`. Let `s : Shuffle p q`, `α ∈ S_p`, `β ∈ S_q`, and `γ ∈ S_N` satisfy
`s.perm * blockPermutation p q α β = γ`. Then `α = blockRankLeft p q γ`, `β = blockRankRight p
q γ`, and `s = sortedBlockShuffle p q γ`.
