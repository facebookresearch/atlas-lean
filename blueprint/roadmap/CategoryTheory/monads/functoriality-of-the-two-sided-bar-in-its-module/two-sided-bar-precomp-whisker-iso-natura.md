# Two Sided Bar Precomp Whisker Iso naturality app op mk

Smallest robust naturality in module maps, at `op (mk n)` components.

Whiskered maps commute with the whisker comparison; the precomposed left-module map is
`(LeftModule.precompFunctor H).map fL`. This component naturality is reused by the product-level
`twoSidedBarPrecompWhiskerNatIso`; identity/composition coherence in `H` is proved at components
in `PrecompProductNaturality` (all components are identities, so the associator
triangle/double-associator pentagon close by `simp`, with correct contravariant `J ⋙ H` source
order).
