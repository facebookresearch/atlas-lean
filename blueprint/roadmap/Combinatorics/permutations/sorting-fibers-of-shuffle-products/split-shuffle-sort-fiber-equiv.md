# The block fiber is the same pair of sorting fibers

Let `p,q,m : ℕ`, `N = p+q`, `γ ∈ S_N`, and `s_f = Tuple.sort f` for a labeling `f : Fin N →
Fin m`. A `(p,q)`-shuffle is a permutation increasing on each of the two input blocks. Put `α
= blockRankLeft p q γ` and `β = blockRankRight p q γ`. The fiber `SplitShuffleSortFiber p q m
γ` is equivalent to the labeling fibers `sort g=α` and `sort h=β`. The forward map keeps
`(g,h)`; its inverse uses the shuffle `sortedBlockShuffle p q γ`.
