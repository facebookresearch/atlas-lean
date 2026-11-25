# Two Sided Bar Iso precomp Comp hom app

Bar-level composition coherence for the module side of source whiskering.

`LeftModule.precompComp H J` lifts through `twoSidedBarIso` to a degreewise-identity bar iso,
preserving the orientation `(L.precomp H).precomp J ≅ L.precomp (J ⋙ H)`. Functor-level
whisker-composite coherence is `twoSidedBarPrecompWhiskerNatIso_comp`, with degree-`n` corollary
`twoSidedBarPrecompWhiskerIso_comp_hom_app` and component consequence
`twoSidedBarPrecompWhiskerIso_comp_hom_app_app`: the two iterated whisker comparisons (with
correct contravariant `J ⋙ H` order) followed by this module bridge coincide with the single `J ⋙
H` comparison, using composition-preservation for `functorPrecompOuter` (alias for Mathlib's
`whiskeringLeft`) together with the double-associator pentagon, all via componentwise identities.
