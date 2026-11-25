# Two Sided Bar Iso precomp Id hom app

Bar-level identity coherence for the module side of source whiskering.

`LeftModule.precompId` lifts through `twoSidedBarIso` to a degreewise-identity bar iso. The
whisker comparison itself remains the double-associator component recorded in
`twoSidedBarPrecompWhiskerIso_hom_app_op_mk`; only the precomposed module is identified here.
Functor-level whisker-composite coherence is `twoSidedBarPrecompWhiskerNatIso_id`, with degree-`n`
corollary `twoSidedBarPrecompWhiskerIso_id_hom_app` and component consequence
`twoSidedBarPrecompWhiskerIso_id_hom_app_app`: the identity whisker and this module bridge compose
to the identity, using identity-preservation for `functorPrecompOuter` (alias for Mathlib's
`whiskeringLeft`) together with the associator triangle, all via componentwise identities.
