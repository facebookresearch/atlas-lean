# Precomp Comp

Composition coherence for outer source whiskering as a natural isomorphism. For `K : B ⥤ A` and `L
: B₂ ⥤ B`, this is `precomp K ⋙ precomp L ≅ precomp (L ⋙ K)`. Reuses the functors and the
objectwise `precompCompIso` (definitionally the associator pair); only the coherence needed by the
bar consumer is packaged.
