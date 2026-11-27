# Two Sided Bar Postcomp Whisker Iso naturality app op mk

Smallest robust naturality in module maps, at `op (mk n)` components.

Whiskered maps commute with the whisker comparison; the postcomposed right-module map is
`(RightModule.postcompFunctor K).map fR`. This component naturality is reused by the product-level
`twoSidedBarPostcompWhiskerNatIso`; identity/composition coherence in `K` is proved at components
in `PostcompProductNaturality` (all components are identities, so the associator triangle/pentagon
close by `simp`).
