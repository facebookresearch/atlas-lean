# The two-block sorting and shuffle fiber

Let `p,q,m : ℕ`, `N = p+q`, `γ ∈ S_N`, and `s_f = Tuple.sort f` for a labeling `f : Fin N →
Fin m`. A `(p,q)`-shuffle is a permutation increasing on each of the two input blocks.
`SplitShuffleSortFiber p q m γ` consists of triples `(s,g,h)` with `s : Shuffle p q`, `g : Fin
p → Fin m`, `h : Fin q → Fin m`, and `s.perm * blockPermutation p q (Tuple.sort g) (Tuple.sort
h) = γ`.
