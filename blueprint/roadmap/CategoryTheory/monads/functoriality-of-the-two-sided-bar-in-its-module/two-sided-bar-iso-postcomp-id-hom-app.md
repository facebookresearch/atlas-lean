# Two Sided Bar Iso postcomp Id hom app

Bar-level identity coherence for the module side of target whiskering.

`RightModule.postcompId` lifts through `twoSidedBarIso` to a degreewise-identity bar iso. The
whisker comparison itself remains the `Functor.associator` component recorded in
`twoSidedBarPostcompWhiskerIso_hom_app_op_mk`; only the postcomposed module is identified here.
Functor-level whisker-composite coherence is `twoSidedBarPostcompWhiskerNatIso_id`, with
degree-`n` corollary `twoSidedBarPostcompWhiskerIso_id_hom_app` and component consequence
`twoSidedBarPostcompWhiskerIso_id_hom_app_app`: the identity whisker and this module bridge
compose to the identity, using identity-preservation for `functorPostcompOuter` (alias for
Mathlib's `whiskeringRight`) together with the associator triangle, all via componentwise
identities.
