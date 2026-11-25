# Natural Multiplication

For the tensor system `N` and cycle complexes `T` over a field $k$, the multiplication
$\mathbb{Z}(q) \otimes \mathbb{Z}(r) \to \mathbb{Z}(q + r)$ of the Tate complexes with $q, r \ge 0$
(`naturalTateComplex`: the singular chain complex `torusChains` of the reduced torus, placed in
nonpositive degrees and shifted by $-q$), as a cochain map from their total tensor complex: the
tensor-shift isomorphism `tensorShiftIso` (with its Koszul signs), followed by the comparison `V`
between the tensor of the extended chain complexes and the extended chain-level tensor, and by the
extension of the chain-level product `unshiftedMultiplication` (the Eilenberg–Zilber shuffle map
`Z` followed by the external cycle product `M`), both shifted by $-(q + r)$.
