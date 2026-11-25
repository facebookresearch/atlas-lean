# Two Sided Bar Precomp Whisker Iso comp hom app

Degree-`n` component of composition whisker coherence, with
correct contravariant order `(L.precomp H).precomp J ≅ L.precomp (J ⋙ H)`.

The `J`-whiskering of the `H` comparison, followed by the `J` comparison and
the module-side `precompComp` bridge, coincides with the single `J ⋙ H`
comparison at `op (mk n)`; see `twoSidedBarPrecompWhiskerNatIso_comp` for the
functor-level statement. All sides have identity components, so Mathlib's
double-associator pentagon closes by `simp`; the ambient
`functorPrecompOuterComp` bridge is likewise componentwise identity, with
Mathlib refl alias `whiskeringLeftObjCompIso` in symm orientation.
