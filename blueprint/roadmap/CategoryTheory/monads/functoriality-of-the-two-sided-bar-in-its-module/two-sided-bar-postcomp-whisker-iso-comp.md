# Two Sided Bar Postcomp Whisker Iso comp hom app

Degree-`n` component of composition whisker coherence, with the
orientation `postcomp K ⋙ postcomp Q ≅ postcomp (K ⋙ Q)`.

The `Q`-whiskering of the `K` comparison, followed by the `Q` comparison and
the module-side `postcompComp` bridge, coincides with the single `K ⋙ Q`
comparison at `op (mk n)`; see `twoSidedBarPostcompWhiskerNatIso_comp` for the
functor-level statement. All sides have identity components, so Mathlib's
associator pentagon closes by `simp`; the ambient
`functorPostcompOuterComp` bridge is likewise componentwise identity.
