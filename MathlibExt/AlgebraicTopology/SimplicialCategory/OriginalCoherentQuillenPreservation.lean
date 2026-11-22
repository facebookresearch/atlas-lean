/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentQuillenAdjunction
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentNerveDwyerKan
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# Same-map consequences of the original coherent Quillen adjunction

Actual original categorical weak maps have DK-weak coherent
realizations. The SAME original coherent nerve preserves all
original Bergner fibrations and trivial fibrations, and recognizes
the original weak class between genuinely fibrant enrichments.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison
open SimplicialEnrichment
attribute [local instance] JoyalSSet.modelCategory Bergner.modelCategory

private theorem allObjectsCofibrant (K : JoyalSSet.{u}) : IsCofibrant K := by
  let i : JoyalSSet.ofSSet.{u}.obj (⊥_ SSet.{u}) ⟶ K :=
    InducedCategory.homMk (initial.to K.toSSet)
  have hm : Mono i := by
    let _ : Mono (initial.to K.toSSet) := inferInstance
    apply JoyalSSet.forget.mono_of_mono_map
    change Mono (initial.to K.toSSet)
    infer_instance
  let hInitial : IsInitial (JoyalSSet.ofSSet.{u}.obj (⊥_ SSet.{u})) :=
    (initialIsInitial (C := SSet.{u})).isInitialObj JoyalSSet.ofSSet.{u} (⊥_ SSet.{u})
  apply (isCofibrant_iff_of_isInitial i hInitial).mpr
  rw [HomotopicalAlgebra.cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations i
  rw [JoyalSSet.modelCategory_cofibrations]
  exact hm

/-- Every SAME original categorical weak map has its genuine original coherent realization DK weak. -/
theorem realizationMap_weak_of_categorical {K L : SSet.{u}} (f : K ⟶ L)
    (hf : SSet.categoricalEquivalences f) :
    EnrichedDwyerKan.weakEquivalences (realizationFunctor.map f) := by
  let _ : adjunction.{u}.IsQuillenAdjunction := isQuillenAdjunction
  let X := JoyalSSet.ofSSet.obj K
  let Y := JoyalSSet.ofSSet.obj L
  let _ : IsCofibrant X := allObjectsCofibrant X
  let _ : IsCofibrant Y := allObjectsCofibrant Y
  let _ : WeakEquivalence (JoyalSSet.ofSSet.map f) := by
    rw [weakEquivalence_iff]
    change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences (JoyalSSet.ofSSet.map f)
    rw [JoyalSSet.modelCategory_weakEquivalences]
    exact hf
  have h : WeakEquivalence (left.map (JoyalSSet.ofSSet.map f)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adjunction) (JoyalSSet.ofSSet.map f)
  exact (Bergner.weakEquivalence_iff_original _).mp h

/-- The SAME original coherent nerve preserves EVERY full original Bergner fibration. -/
theorem nerve_categoricalFibration_of_original {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : Bergner.localFibrations F) :
    SSet.categoricalFibrations (coherentNerveFunctor.map F) := by
  let _ : adjunction.{u}.IsQuillenAdjunction := isQuillenAdjunction
  have h : fibrations JoyalSSet.{u} (right.map F) :=
    Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adjunction) F hF
  change JoyalSSet.modelCategory.categoryWithFibrations.fibrations (right.map F) at h
  rw [JoyalSSet.modelCategory_fibrations] at h
  exact h

/-- The SAME original coherent nerve preserves the actual full original trivial-fibration intersection. -/
theorem nerve_categoricalTrivialFibration_of_original {C D : Carrier.{u}} (F : C ⟶ D)
    (hF : Bergner.localFibrations F ∧ EnrichedDwyerKan.weakEquivalences F) :
    SSet.categoricalFibrations (coherentNerveFunctor.map F) ∧
      SSet.categoricalEquivalences (coherentNerveFunctor.map F) := by
  let _ : adjunction.{u}.IsQuillenAdjunction := isQuillenAdjunction
  have h : trivialFibrations JoyalSSet.{u} (right.map F) :=
    Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := adjunction) F hF
  have hFib := h.1
  have hWeak := h.2
  change JoyalSSet.modelCategory.categoryWithFibrations.fibrations (right.map F) at hFib
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences (right.map F) at hWeak
  rw [JoyalSSet.modelCategory_fibrations] at hFib
  rw [JoyalSSet.modelCategory_weakEquivalences] at hWeak
  exact ⟨hFib,hWeak⟩

/-- At genuinely original full locally Kan enrichments the SAME nerve recognizes precisely the full original DK weak
class. -/
theorem nerve_weak_iff_original {C D : Carrier.{u}} (F : C ⟶ D)
    (hC : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (hD : ∀ x y : D, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.categoricalEquivalences (coherentNerveFunctor.map F) ↔ EnrichedDwyerKan.weakEquivalences F := by
  let R := ComponentHomotopyCategory.readFunctor C
  let S := ComponentHomotopyCategory.readFunctor D
  let M := ComponentCategory.mapFunctor F
  let N := SSet.mapHomotopyCategory (coherentNerveFunctor.map F)
  let _ : R.IsEquivalence := ComponentHomotopyCategory.isEquivalence C hC
  let _ : S.IsEquivalence := ComponentHomotopyCategory.isEquivalence D hD
  have hNat : N ⋙ S = R ⋙ M := ComponentHomotopyCategory.naturality F
  have hEss : N.EssSurj ↔ M.EssSurj := by
    constructor
    · intro h
      let _ : N.EssSurj := h
      have hComp : (R ⋙ M).EssSurj := hNat ▸ (inferInstance : (N ⋙ S).EssSurj)
      constructor
      intro y
      exact (Functor.essImage_comp_apply_of_essSurj (F := R) (G := M) (X := y)).mp
        (hComp.mem_essImage y)
    · intro h
      let _ : M.EssSurj := h
      let _ : (N ⋙ S).EssSurj := hNat.symm ▸ (inferInstance : (R ⋙ M).EssSurj)
      exact Functor.essSurj_of_comp_fully_faithful N S
  exact (NerveDwyerKan.nerve_categoricalEquivalence_iff F hC hD).trans
    ((and_congr hEss Iff.rfl).trans and_comm)

/-- The SAME actual right map recognizes original model weakness between genuine original fibrant objects. -/
theorem right_weak_iff {C D : Carrier.{u}} (F : C ⟶ D)
    [IsFibrant C] [IsFibrant D] :
    WeakEquivalence (right.map F) ↔ WeakEquivalence F := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences (right.map F) ↔
    EnrichedDwyerKan.weakEquivalences F
  rw [JoyalSSet.modelCategory_weakEquivalences]
  exact nerve_weak_iff_original F (Bergner.homKan_of_isFibrant C) (Bergner.homKan_of_isFibrant D)

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
