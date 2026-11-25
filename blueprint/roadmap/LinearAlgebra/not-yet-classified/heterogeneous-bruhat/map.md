# Map

Coefficient-functorial image of a heterogeneous Bruhat decomposition.

Given `f : K →+* L`, `e : GeneralLinearEquiv m n K` and
`d : HeterogeneousBruhatDecomposition e` with factorization
`e = ((ofGL left).trans (monomialEquiv weights perm)).trans (ofGL right)`,
`d.map f` is the decomposition of `e.map f` whose left/right factors are
`UpperElementary.mapRingHom f left/right`, whose weights are
`Units.map f ∘ weights`, whose permutation is the same, and whose
factorization follows from `d.factorization`, `GeneralLinearEquiv.map_trans`,
`GeneralLinearEquiv.map_monomialEquiv`, and the GL/upper map lemmas.
This maps an arbitrary decomposition only; no claim about the canonical
choice `heterogeneousBruhatDecomposition` is made.
