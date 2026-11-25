# Projective Resolution Unop Inj

The unopposite of a projective resolution in `Cᵒᵖ` is an injective
resolution (dual of `injectiveResolutionOpProj`).

Informal sketch: unop the complex (projectives dualize to injectives via the
Mathlib instance); the augmentation is `single₀UnopIso` followed by the unop'd
`π` (a quasi-iso since `unopFunctor` preserves quasi-isos). Stated over a
general `Y : Cᵒᵖ` (rather than `op X`) with the same baked instances as the
horseshoe endpoint ascriptions, so horseshoe-middle applications match
syntactically.
