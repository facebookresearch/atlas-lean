# Tensor Hom eq map Bifunctor Map

In the monoidal category of homological complexes, `⊗ₘ` is the totalization of the two
morphisms.  Mathlib defines `HomologicalComplex.monoidalCategory` this way, but states no lemma
exposing it, so `HomologicalComplex.ι_tensorHom` does not apply to `⊗ₘ` without this rewrite.
