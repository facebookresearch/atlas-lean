# The global fiber is a pair of rank sorting fibers

Let `p,q,m : ℕ`, `N = p+q`, `γ ∈ S_N`, and `s_f = Tuple.sort f` for a labeling `f : Fin N →
Fin m`. A `(p,q)`-shuffle is a permutation increasing on each of the two input blocks. Put `α
= blockRankLeft p q γ`, `β = blockRankRight p q γ`, and `s_γ = sortedBlockShuffle p q γ`. The
fiber `ShuffleSortFiber p q m γ` is equivalent to `{g : Fin p → Fin m // sort g=α} × {h : Fin
q → Fin m // sort h=β}` by restricting its labeling along the value blocks of `s_γ`.
