# Two Sided Bar Precomp Whisker Nat Iso comp

Functor-level composition coherence for source precomposition, with correct
contravariant order `(L.precomp H).precomp J ≅ L.precomp (J ⋙ H)`.

The `J`-whiskering of the `H` comparison, followed by the `J` comparison at
the precomposed module and the product-level `precompComp` bridge, equals the
single `J ⋙ H` comparison up to the ambient `functorPrecompOuterComp`
coherence (direct use of `(Functor.whiskeringLeftObjCompIso J H).symm`); no
`R`, `L`, `n`, or `Δ` is bound. The degree-`n` corollary is
`twoSidedBarPrecompWhiskerIso_comp_hom_app`. No pseudofunctor is built.
