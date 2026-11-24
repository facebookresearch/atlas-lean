# To Stable E torus fin last pi Hom mem finite Stage sup ker iff

Membership of a torus preimage in the kernel-joined finite stage
`finiteStage n ⊔ ker toStableE` iff the coordinate product is `1`.

This corrects the boundary torus/stage membership by joining with
`ker toStableE` via `comap_fromFinite_range_eq_finiteStage_sup_ker`;
it does not need or claim injectivity of `toStableE`. Uniform for
`n = 0` (empty product is `1`) and `n = 1`, valid in characteristic
two. This does not claim
`g ∈ finiteStage n ↔ Finset.univ.prod u = 1`, equivalently it
does not drop the required `⊔ ker toStableE` correction, exact torus
multiplication in `StableSteinberg` (defect is central),
commutativity in `StableSteinberg`, or triviality of the kernel; it
holds only after `toStableE` / in `StableE` via `hg`.
