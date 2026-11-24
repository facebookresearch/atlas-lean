# Mapped Cocomplex

The complex computing the right-derived functors: `preadditiveCoyoneda`
applied to an injective resolution. Its degree-`n` term is the group of
morphisms `X ⟶ R.cocomplex.X n`, with postcomposition differentials.

This is an `abbrev` (reducible) rather than a `def` so that rewrites of index
equalities never see a semireducible unfolding in their motive: all dependent
motive checks below run at `implicit` transparency.
