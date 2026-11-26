# The fiber equation determines the rank shuffle

Let `p,q,m : ℕ`, `N = p+q`, `γ ∈ S_N`, and `s_f = Tuple.sort f` for a labeling `f : Fin N →
Fin m`. A `(p,q)`-shuffle is a permutation increasing on each of the two input blocks. For
`z=(f,s) : ShuffleSortFiber p q m γ`, `(Tuple.sort f)⁻¹ * γ = s.perm`.
