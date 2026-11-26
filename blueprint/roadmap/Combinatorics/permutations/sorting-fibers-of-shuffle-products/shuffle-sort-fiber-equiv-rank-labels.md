# The shuffle fiber is its rank-labeling set

Let `p,q,m : ℕ`, `N = p+q`, `γ ∈ S_N`, and `s_f = Tuple.sort f` for a labeling `f : Fin N →
Fin m`. A `(p,q)`-shuffle is a permutation increasing on each of the two input blocks. There
is an equivalence from `ShuffleSortFiber p q m γ` to `{f : Fin N → Fin m // IsShuffle (s_f⁻¹ *
γ)}`. It forgets the shuffle; its inverse equips `f` with the shuffle whose permutation is
`s_f⁻¹ * γ`.
