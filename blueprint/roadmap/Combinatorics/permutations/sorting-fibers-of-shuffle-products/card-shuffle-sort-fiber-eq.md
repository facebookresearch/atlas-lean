# The two shuffle composition fibers have equal size

Let `p,q,m : ℕ`, `N = p+q`, `γ ∈ S_N`, and `s_f = Tuple.sort f` for a labeling `f : Fin N →
Fin m`. A `(p,q)`-shuffle is a permutation increasing on each of the two input blocks. The
cardinalities agree: `Fintype.card (ShuffleSortFiber p q m γ) = Fintype.card
(SplitShuffleSortFiber p q m γ)`.
