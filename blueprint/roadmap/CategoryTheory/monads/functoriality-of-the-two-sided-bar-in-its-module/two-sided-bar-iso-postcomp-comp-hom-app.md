# Two Sided Bar Iso postcomp Comp hom app

Bar-level composition coherence for the module side of target whiskering.

`RightModule.postcompComp K Q` lifts through `twoSidedBarIso` to a degreewise-identity bar iso,
preserving the orientation `(R.postcomp K).postcomp Q ≅ R.postcomp (K ⋙ Q)`.
Functor-level whisker-composite coherence is `twoSidedBarPostcompWhiskerNatIso_comp`, with
degree-`n` corollary `twoSidedBarPostcompWhiskerIso_comp_hom_app` and component consequence
`twoSidedBarPostcompWhiskerIso_comp_hom_app_app`: the two iterated whisker comparisons followed by
this module bridge coincide with the single `K ⋙ Q` comparison, using composition-preservation for
`functorPostcompOuter` (alias for Mathlib's `whiskeringRight`) together with the associator
pentagon, all via componentwise identities.
