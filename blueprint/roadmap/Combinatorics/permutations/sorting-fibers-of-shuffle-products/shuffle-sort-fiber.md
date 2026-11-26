# The global sorting and shuffle fiber

Let `p,q,m : ℕ`, `N = p+q`, `γ ∈ S_N`, and `s_f = Tuple.sort f` for a labeling `f : Fin N →
Fin m`. A `(p,q)`-shuffle is a permutation increasing on each of the two input blocks.
`ShuffleSortFiber p q m γ` consists of pairs `(f,s)` with `s : Shuffle p q` and `s_f * s.perm
= γ`.
