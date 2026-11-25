/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>
module

public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFibrantCriterion

/-!
# Quillen adjunctions between recognized left Bousfield localizations

The original adjunction is Quillen for the recognized localized models exactly
when its right adjoint sends every target local-fibrant object to a source
local-fibrant object. The original adjunction is transported by composing
Mathlib adjunctions of categorical equivalences; its maps are not replaced by
derived maps in this recognition step.

Adapted from the Formal-Math development by Tsutomu Okano.
-/

@[expose] public section

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra.LeftBousfieldLocalization

variable {C D : Type*} [Category* C] [ModelCategory C] [Category* D] [ModelCategory D]
  {W : MorphismProperty C} {V : MorphismProperty D} {P : ObjectProperty C} {Q : ObjectProperty D}
  (source : Recognition W P) (target : Recognition V Q)
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The original adjunction transported to the tagged carriers. -/
def localizedAdjunction :
    ((equivalence source).inverse ⋙ (F ⋙ (equivalence target).functor)) ⊣
      (((equivalence target).inverse ⋙ G) ⋙ (equivalence source).functor) :=
  (equivalence source).symm.toAdjunction.comp (adj.comp (equivalence target).toAdjunction)

/-- With the original adjunction Quillen, the localized adjunction is Quillen
if and only if the right adjoint preserves the full target local-fibrant
predicate. The models on the tagged carriers are constructed from recognition
data, not supplied as hypotheses. -/
theorem isQuillenAdjunction_iff_preservesLocalFibrant [adj.IsQuillenAdjunction] :
    (localizedAdjunction source target adj).IsQuillenAdjunction ↔
      ∀ Z : D, Q Z → P (G.obj Z) := by
  constructor
  · intro h Z hZ
    let object := (equivalence target).functor.obj Z
    have : IsFibrant object := (isFibrant_iff target object).mpr hZ
    exact (isFibrant_iff source _).mp
      ((Adjunction.IsQuillenAdjunction.preservesFibrantObjects
        (adj := localizedAdjunction source target adj)).isFibrant (X := object) inferInstance)
  · intro h
    apply Adjunction.IsQuillenAdjunction.mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects
      (adj := localizedAdjunction source target adj)
    · intro X Y f hf
      exact Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := adj) f.hom hf
    · intro X Y p hp
      have hX := (isFibrant_iff target X).mp hp.2.1
      have hY := (isFibrant_iff target Y).mp hp.2.2
      apply (fibration_iff_of_local source _ (h X.1 hX) (h Y.1 hY)).mpr
      exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adj) p.hom
        ((fibration_iff_of_local target p hX hY).mp hp.1)

end HomotopicalAlgebra.LeftBousfieldLocalization
